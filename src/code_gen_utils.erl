-module(code_gen_utils).
-export([
  '_@gm_spawn'/1,
  '_@gm_run'/1,
  '_@gm_find'/2,
  '_@gm_set'/3,
  '_@curry'/3,
  '_@wrap_with_impls'/5,
  '_@concat'/2,
  '_@separate'/2
]).
-compile(no_auto_import).

'_@gm_spawn'(Gm) ->
  case erlang:whereis(Gm) of
    undefined ->
      Pid = erlang:spawn(fun() -> '_@gm_run'(#{}) end),
      erlang:register(Gm, Pid);

    Pid ->
      Pid ! {erlang:self(), reset},
      receive
        reset_ok -> true;
        Unexpected ->
          erlang:error({"unexpected reset response", Gm, Unexpected})
      after 1000 ->
        erlang:error({"couldn't reset globals", Gm})
      end
  end.

'_@gm_run'(Globals) ->
  receive
    {Pid, reset} ->
      Pid ! reset_ok,
      '_@gm_run'(#{});
    {Pid, get, Atom} ->
      Pid ! {get_ok, maps:get(Atom, Globals)},
      '_@gm_run'(Globals);
    {Pid, find, Atom} ->
      Pid ! {find_ok, maps:find(Atom, Globals)},
      '_@gm_run'(Globals);
    {Pid, set, Atom, Value} ->
      Pid ! set_ok,
      '_@gm_run'(Globals#{Atom => Value});
    Unexpected ->
      io:format("unexpected gm message ~p~n", [Unexpected]),
      '_@gm_run'(Globals)
  end.

'_@gm_find'(Gm, Atom) ->
  Gm ! {erlang:self(), find, Atom},
  receive
    {find_ok, Result} -> Result;
    Unexpected ->
      erlang:error({"unexpected find response", Gm, Atom, Unexpected})
  after 1000 ->
    erlang:error({"couldn't find global", Gm, Atom})
  end.

'_@gm_set'(Gm, Atom, Value) ->
  Gm ! {erlang:self(), set, Atom, Value},
  receive
    set_ok -> Value;
    Unexpected ->
      erlang:error({"unexpected set response", Gm, Atom, Value, Unexpected})
  after 1000 ->
    erlang:error({"couldn't set global", Gm, Atom, Value})
  end.

'_@curry'(Fun, RawArgs, Line) ->
  {arity, Arity} = erlang:fun_info(Fun, arity),

  Args = case Arity of
    0 ->
      {} = erlang:hd(RawArgs),
      erlang:tl(RawArgs);
    _ -> RawArgs
  end,
  NumArgs = erlang:length(Args),

  if
    NumArgs < Arity ->
      NewArgsRep = lists:map(fun(Num) ->
        {var, Line, erlang:list_to_atom(lists:concat(["_@Arg", Num]))}
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

    NumArgs == Arity -> erlang:apply(Fun, Args);

    NumArgs > Arity ->
      {ImmArgs, RestArgs} = lists:split(Arity, Args),
       '_@curry'(erlang:apply(Fun, ImmArgs), RestArgs, Line)
  end.

'_@wrap_with_impls'(Fun, PatternReps, ImplReps, BindList, Line) ->
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

  '_@wrap_with_impls_r'(Fun, PatternReps, ArgsWithImplsRep, Bindings, Line).

'_@wrap_with_impls_r'(Fun, PatternReps, ArgsWithImplsRep, Bindings, Line) ->
  {arity, Arity} = erlang:fun_info(Fun, arity),
  FullArity = erlang:length(PatternReps),

  FunAtom = '_@Fun',
  FunVarRep = {var, Line, FunAtom},
  Bindings1 = erl_eval:add_binding(FunAtom, Fun, Bindings),
  Call = {call, Line, FunVarRep, lists:sublist(ArgsWithImplsRep, Arity)},

  {Body, FinalBindings} = if
    FullArity == Arity -> {[Call], Bindings1};

    FullArity > Arity ->
      BindingsToAdd = [
        {'_@Recur', fun '_@wrap_with_impls_r'/5},
        {'_@PatternReps', lists:sublist(PatternReps, Arity + 1, FullArity)},
        {'_@ArgsWithImplsRep', lists:sublist(ArgsWithImplsRep, Arity + 1, FullArity)},
        {'_@Bindings', Bindings},
        {'_@Line', Line}
      ],

      {BindingReps, Bindings2} = lists:mapfoldl(fun({Atom, Value}, FoldBindings) ->
        Var = {var, Line, Atom},
        {Var, erl_eval:add_binding(Atom, Value, FoldBindings)}
      end, Bindings1, BindingsToAdd),

      RecurVarRep = erlang:hd(BindingReps),
      RecurArgsRep = [Call | erlang:tl(BindingReps)],
      RecurCall = {call, Line, RecurVarRep, RecurArgsRep},
      {[RecurCall], Bindings2}

    % FullArity is the *most* number of args Fun could have; it should never be
    % less than Arity.
  end,

  Clause = {clause, Line, lists:sublist(PatternReps, Arity), [], Body},
  Expr = {'fun', Line, {clauses, [Clause]}},
  {value, Value, _} = erl_eval:expr(Expr, FinalBindings),
  Value.

'_@concat'(Left, Right) ->
  if
    erlang:is_binary(Left) -> <<Left/binary, Right/binary>>;
    erlang:is_list(Left) -> Left ++ Right;
    erlang:is_map(Left) -> maps:merge(Left, Right)
  end.

'_@separate'(Left, Right) ->
  if
    erlang:is_list(Left) ->
      Set = gb_sets:from_list(Right),
      lists:filter(fun(Elem) ->
        not gb_sets:is_element(Elem, Set)
      end, Left);
    erlang:is_map(Left) -> maps:without(maps:keys(Right), Left)
  end.
