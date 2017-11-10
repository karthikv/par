-module(par_native).
-export([
  init/1,
  gm_spawn/0,
  gm_run/1,
  gm_find/2,
  gm_set/3,
  curry/3,
  wrap_with_impls/5,
  concat/2,
  separate/2
]).

init(Mod) ->
  gm_spawn(),
  Mod:'_@init'(ordsets:new()).

gm_spawn() ->
  case whereis(par_gm) of
    undefined ->
      Pid = spawn(fun() -> gm_run(#{}) end),
      register(par_gm, Pid);

    Pid ->
      Pid ! {self(), reset},
      receive
        reset_ok -> true;
        Unexpected -> error({"unexpected reset response", Unexpected})
      after 1000 -> error("couldn't reset globals")
      end
  end.

gm_run(Globals) ->
  receive
    {Pid, reset} ->
      Pid ! reset_ok,
      gm_run(#{});
    {Pid, get, Key} ->
      Pid ! {get_ok, maps:get(Key, Globals)},
      gm_run(Globals);
    {Pid, find, Key} ->
      Pid ! {find_ok, maps:find(Key, Globals)},
      gm_run(Globals);
    {Pid, set, Key, Value} ->
      Pid ! set_ok,
      gm_run(Globals#{Key => Value});
    Unexpected ->
      io:format("unexpected gm message ~p~n", [Unexpected]),
      gm_run(Globals)
  end.

gm_find(Mod, Atom) ->
  Key = {Mod, Atom},
  par_gm ! {self(), find, Key},
  receive
    {find_ok, Result} -> Result;
    Unexpected -> error({"unexpected find response", Key, Unexpected})
  after 1000 -> error({"couldn't find global", Key})
  end.

gm_set(Mod, Atom, Value) ->
  Key = {Mod, Atom},
  par_gm ! {self(), set, Key, Value},
  receive
    set_ok -> Value;
    Unexpected -> error({"unexpected set response", Key, Value, Unexpected})
  after 1000 -> error({"couldn't set global", Key, Value})
  end.

curry(Fun, RawArgs, Line) ->
  {arity, Arity} = erlang:fun_info(Fun, arity),

  Args = case Arity of
    0 ->
      {} = hd(RawArgs),
      tl(RawArgs);
    _ -> RawArgs
  end,
  NumArgs = length(Args),

  if
    NumArgs < Arity ->
      NewArgsRep = lists:map(fun(Num) ->
        {var, Line, list_to_atom(lists:concat(["_@Arg", Num]))}
      end, lists:seq(NumArgs + 1, Arity)),
      NewArgsListRep = lists:foldr(fun(FoldArgRep, FoldListRep) ->
        {cons, Line, FoldArgRep, FoldListRep}
      end, {nil, Line}, NewArgsRep),

      FunVar = {var, Line, '_@Fun'},
      ArgsVar = {var, Line, '_@Args'},

      Body = [{call, Line,
        {remote, Line, {atom, Line, erlang}, {atom, Line, apply}},
        [FunVar, {op, Line, '++', ArgsVar, NewArgsListRep}]}],
      Clause = {clause, Line, NewArgsRep, [], Body},
      Expr = {'fun', Line, {clauses, [Clause]}},

      Bindings = lists:foldl(fun({{var, _, Atom}, Value}, FoldBindings) ->
        erl_eval:add_binding(Atom, Value, FoldBindings)
      end, erl_eval:new_bindings(), [{FunVar, Fun}, {ArgsVar, Args}]),

      {value, Value, _} = erl_eval:expr(Expr, Bindings),
      Value;

    NumArgs == Arity -> apply(Fun, Args);

    NumArgs > Arity ->
      {ImmArgs, RestArgs} = lists:split(Arity, Args),
      curry(apply(Fun, ImmArgs), RestArgs, Line)
  end.

wrap_with_impls(Fun, PatternReps, ImplReps, BindList, Line) ->
  Bindings = lists:foldl(fun({Atom, Value}, FoldBindings) ->
    erl_eval:add_binding(Atom, Value, FoldBindings)
  end, erl_eval:new_bindings(), BindList),

  ArgsWithImplsRep = lists:map(fun({PatternRep, ArgImplReps}) ->
    ArgRep = case PatternRep of
      {tuple, _, [ArgRep_ | _]} -> ArgRep_;
      _ -> PatternRep
    end,
    case ArgImplReps of
      [] -> ArgRep;
      _ -> {tuple, Line, [ArgRep | ArgImplReps]}
    end
  end, lists:zip(PatternReps, ImplReps)),

  wrap_with_impls_r(Fun, PatternReps, ArgsWithImplsRep, Bindings, Line).

wrap_with_impls_r(Fun, PatternReps, ArgsWithImplsRep, Bindings, Line) ->
  {arity, Arity} = erlang:fun_info(Fun, arity),
  FullArity = length(PatternReps),

  FunAtom = '_@Fun',
  FunVarRep = {var, Line, FunAtom},
  Bindings1 = erl_eval:add_binding(FunAtom, Fun, Bindings),
  Call = {call, Line, FunVarRep, lists:sublist(ArgsWithImplsRep, Arity)},

  {Body, FinalBindings} = if
    FullArity == Arity -> {[Call], Bindings1};

    FullArity > Arity ->
      BindingsToAdd = [
        {'_@Recur', fun wrap_with_impls_r/5},
        {'_@PatternReps', lists:sublist(PatternReps, Arity + 1, FullArity)},
        {'_@ArgsWithImplsRep', lists:sublist(ArgsWithImplsRep, Arity + 1, FullArity)},
        {'_@Bindings', Bindings},
        {'_@Line', Line}
      ],

      {BindingReps, Bindings2} = lists:mapfoldl(fun({Atom, Value}, FoldBindings) ->
        Var = {var, Line, Atom},
        {Var, erl_eval:add_binding(Atom, Value, FoldBindings)}
      end, Bindings1, BindingsToAdd),

      RecurVarRep = hd(BindingReps),
      RecurArgsRep = [Call | tl(BindingReps)],
      RecurCall = {call, Line, RecurVarRep, RecurArgsRep},
      {[RecurCall], Bindings2}

    % FullArity is the *most* number of args Fun could have; it should never be
    % less than Arity.
  end,

  Clause = {clause, Line, lists:sublist(PatternReps, Arity), [], Body},
  Expr = {'fun', Line, {clauses, [Clause]}},
  {value, Value, _} = erl_eval:expr(Expr, FinalBindings),
  Value.

concat(Left, Right) ->
  if
    is_binary(Left) -> <<Left/binary, Right/binary>>;
    is_list(Left) -> Left ++ Right;
    is_map(Left) -> maps:merge(Left, Right)
  end.

separate(Left, Right) ->
  if
    is_list(Left) ->
      Map = maps:from_list([{Elem, true} || Elem <- Right]),
      lists:filter(fun(Elem) ->
        not maps:is_key(Elem, Map)
      end, Left);
    is_map(Left) -> maps:without(maps:keys(Right), Left)
  end.
