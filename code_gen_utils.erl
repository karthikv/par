-module(code_gen_utils).
-export([
  '_@gm_spawn'/1,
  '_@gm_run'/1,
  '_@gm_maybe_set'/3,
  '_@gm_get'/2,
  '_@curry'/3,
  '_@concat'/2,
  '_@separate'/2
]).

'_@gm_spawn'(Gm) ->
  case whereis(Gm) of
    undefined ->
      Pid = spawn(fun() -> '_@gm_run'(#{}) end),
      register(Gm, Pid);

    Pid ->
      Pid ! {self(), reset},
      receive
        reset_ok -> true;
        Unexpected ->
          error({"unexpected reset response", Gm, Unexpected})
      after 1000 ->
        error({"couldn't reset globals", Gm})
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

'_@gm_maybe_set'(Gm, Atom, Fun) ->
  Gm ! {self(), find, Atom},
  receive
    {find_ok, {ok, Value}} -> Value;

    {find_ok, error} ->
      Value = Fun(),
      Gm ! {self(), set, Atom, Value},
      receive
        set_ok -> Value;

        Unexpected ->
          error({"unexpected set response", Gm, Atom, Value, Unexpected})
      after 1000 ->
        error({"couldn't set global", Gm, Atom, Value})
      end;

    Unexpected ->
      error({"unexpected find response", Gm, Atom, Unexpected})
  after 1000 ->
    error({"couldn't find global", Gm, Atom})
  end.

'_@gm_get'(Gm, Atom) ->
  Gm ! {self(), get, Atom},
  receive
    {get_ok, Value} -> Value;
    Unexpected ->
      error({"unexpected get response", Gm, Atom, Unexpected})
  after 1000 ->
    error({"couldn't get global", Gm, Atom})
  end.

'_@curry'(Fun, RawArgs, Line) ->
  {arity, Arity} = erlang:fun_info(Fun, arity),

  Args = case Arity of
    0 ->
      none = hd(RawArgs),
      tl(RawArgs);
    _ -> RawArgs
  end,
  NumArgs = length(Args),

  if
    NumArgs < Arity ->
      NewArgsRep = lists:map(fun(Num) ->
        {var, Line, list_to_atom(lists:concat(['_@', Num]))}
      end, lists:seq(NumArgs + 1, Arity)),
      NewArgsListRep = lists:foldr(fun(FoldArgRep, FoldListRep) ->
        {cons, Line, FoldArgRep, FoldListRep}
      end, {nil, Line}, NewArgsRep),

      FunVar = {var, Line, '_@Fun'},
      ArgsVar = {var, Line, '_@Args'},

      Body = [{call, Line, {atom, Line, apply},
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

      case length(RestArgs) of
        0 -> apply(Fun, ImmArgs);
        _ ->
          '_@curry'(apply(Fun, ImmArgs), RestArgs, Line)
      end
  end.

'_@concat'(Left, Right) ->
  if
    is_binary(Left) -> <<Left/binary, Right/binary>>;
    is_list(Left) -> Left ++ Right;
    is_map(Left) -> maps:merge(Left, Right);
    true ->
      true = gb_sets:is_set(Left),
      gb_sets:union(Left, Right)
  end.

'_@separate'(Left, Right) ->
  if
    is_list(Left) ->
      Set = gb_sets:from_list(Right),
      lists:filter(fun(Elem) ->
        not gb_sets:is_member(Elem, Set)
      end, Left);
    true ->
      true = gb_sets:is_set(Left),
      gb_sets:subtract(Left, Right)
  end.
