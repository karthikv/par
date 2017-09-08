-module(code_gen_utils).
-export([
  '_@gm_spawn'/1,
  '_@gm_run'/1,
  '_@gm_find'/2,
  '_@gm_set'/3,
  '_@curry'/3,
  '_@wrap_with_impls'/3,
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
        {var, Line, erlang:list_to_atom(lists:concat(['_@Arg', Num]))}
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

    NumArgs >= Arity ->
      ImmArgs = lists:sublist(Args, Arity),
      RestArgs = lists:sublist(Args, Arity + 1, NumArgs),

      case erlang:length(RestArgs) of
        0 -> erlang:apply(Fun, ImmArgs);
        _ ->
          '_@curry'(erlang:apply(Fun, ImmArgs), RestArgs, Line)
      end
  end.

'_@wrap_with_impls'(Fun, AllImpls, Line) ->
  {arity, Arity} = erlang:fun_info(Fun, arity),
  NumImpls = erlang:length(AllImpls),

  TargetImpls = lists:sublist(AllImpls, Arity),
  {TargetImplsRep, {Bindings, _}} = lists:mapfoldl(fun(ArgImpls, Memo) ->
    lists:mapfoldl(fun(Impl, {FoldBindings, FoldNum}) ->
      Name = lists:concat(['_@Impl', FoldNum]),
      Atom = erlang:list_to_atom(Name),
      VarRep = {var, Line, Atom},

      NewBindings = erl_eval:add_binding(Atom, Impl, FoldBindings),
      NewNum = FoldNum + 1,
      {VarRep, {NewBindings, NewNum}}
    end, Memo, ArgImpls)
  end, {erl_eval:new_bindings(), 0}, TargetImpls),

  ArgsRep = lists:map(fun(Num) ->
    {var, Line, erlang:list_to_atom(lists:concat(['_@Arg', Num]))}
  end, lists:seq(1, Arity)),

  ArgsWithImplsRep = lists:map(fun({ArgRep, ArgImplsRep}) ->
    case ArgImplsRep of
      [] -> ArgRep;
      _ -> {tuple, Line, [ArgRep | ArgImplsRep]}
    end
  end, lists:zip(ArgsRep, TargetImplsRep)),

  FunAtom = '_@Fun',
  Bindings1 = erl_eval:add_binding(FunAtom, Fun, Bindings),
  FunVarRep = {var, Line, FunAtom},

  Call = {call, Line, FunVarRep, ArgsWithImplsRep},
  {Body, FinalBindings} = if
    NumImpls == Arity -> {[Call], Bindings1};

    NumImpls > Arity ->
      LeftImpls = lists:sublist(AllImpls, Arity + 1, NumImpls),
      LeftAtom = '_@LeftImpls',
      LeftVarRep = {var, Line, LeftAtom},
      Bindings2 = erl_eval:add_binding(LeftAtom, LeftImpls, Bindings1),

      RecurAtom = '_@Recur',
      RecurVarRep = {var, Line, RecurAtom},
      RecurFun = fun '_@wrap_with_impls'/3,
      Bindings3 = erl_eval:add_binding(RecurAtom, RecurFun, Bindings2),

      RecurArgsRep = [Call, LeftVarRep, erl_parse:abstract(Line, Line)],
      RecurCall = {call, Line, RecurVarRep, RecurArgsRep},
      {[RecurCall], Bindings3}

    % NumImpls is the *most* number of args Fun could have; it should never be
    % less than Arity.
  end,

  Clause = {clause, Line, ArgsRep, [], Body},
  Expr = {'fun', Line, {clauses, [Clause]}},
  {value, Value, _} = erl_eval:expr(Expr, FinalBindings),
  Value.

'_@concat'(Left, Right) ->
  if
    erlang:is_binary(Left) -> <<Left/binary, Right/binary>>;
    erlang:is_list(Left) -> Left ++ Right;
    erlang:is_map(Left) -> maps:merge(Left, Right);
    true ->
      true = gb_sets:is_set(Left),
      gb_sets:union(Left, Right)
  end.

'_@separate'(Left, Right) ->
  if
    erlang:is_list(Left) ->
      Set = gb_sets:from_list(Right),
      lists:filter(fun(Elem) ->
        not gb_sets:is_member(Elem, Set)
      end, Left);
    true ->
      true = gb_sets:is_set(Left),
      gb_sets:subtract(Left, Right)
  end.
