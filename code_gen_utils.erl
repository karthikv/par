-module(code_gen_utils).
-export([
  '_@ets_create_table'/1,
  '_@ets_lookup_or_insert'/2,
  '_@curry'/3,
  '_@concat'/2,
  '_@separate'/2
]).

'_@ets_create_table'(Atom) ->
  case ets:info(Atom, name) of
    undefined -> ets:new(Atom, [set, named_table]);
    Tab -> Tab
  end.

'_@ets_lookup_or_insert'(Atom, Fun) ->
  case ets:lookup(constants, Atom) of
    [] ->
      Value = Fun(),
      ets:insert(constants, {Atom, Value}),
      Value;
    [{_, Value}] -> Value
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
