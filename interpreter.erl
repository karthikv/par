-module(interpreter).
-export([reload/1, execute/1]).

reload(Syntax) ->
  par:reload(Syntax),

  code:purge(?MODULE),
  {ok, _} = compile:file(?MODULE),
  code:load_file(?MODULE).

execute(Ast) ->
  ID = env_create_first(),
  lists:foreach(fun(Node) -> init(Node, ID) end, Ast),

  lists:foreach(fun(Node) ->
    case Node of
      % strictly evaluate all globals
      {global, Var, _} -> eval(Var, ID);
      _ -> true
    end
  end, Ast),

  eval({app, {var, 0, "main"}, []}, ID).

init({global, {var, _, Name}, Expr}, ID) ->
  env_set(Name, {lazy, Expr}, ID);

init({enum, _, OptionTEs}, ID) ->
  lists:foreach(fun({option, {con_token, _, Name}, ArgsTE}) ->
    Value = if
      length(ArgsTE) == 0 -> list_to_atom(Name);
      true ->
        curry(length(ArgsTE), fun(Vs) ->
          list_to_tuple([list_to_atom(Name) | Vs])
        end, [])
    end,

    env_set(Name, Value, ID)
  end, OptionTEs);

init({struct, StructTE, FieldTEs}, ID) ->
  StructName = case StructTE of
    {con_token, _, Name} -> Name;
    {gen_te, {con_token, _, Name}, _} -> Name
  end,

  FieldNames = lists:map(fun({field, {var, _, FieldName}, _}) ->
    FieldName
  end, FieldTEs),
  Value = curry(length(FieldTEs), fun(Vs) ->
    list_to_tuple([list_to_atom(StructName) | Vs])
  end, []),

  env_set(StructName, {struct, FieldNames, Value}, ID);

init({sig, _, _}, _) -> true.

eval({fn, Args, Expr}, ID) ->
  curry(length(Args), fun(Vs) ->
    NewID = if
      length(Args) == 0 -> ID;
      true ->
        ChildID = env_create_child(ID),
        lists:foreach(fun({{var, _, Name}, V}) ->
          env_set(Name, V, ChildID)
        end, lists:zip(Args, Vs)),
        ChildID
    end,

    eval(Expr, NewID)
  end, []);

eval({expr_sig, Expr, _}, ID) -> eval(Expr, ID);

eval(none, _) -> none;
eval({N, _, V}, _)
  when N == int; N == float; N == bool; N == str; N == atom -> V;

eval({list, Elems}, ID) ->
  lists:map(fun(E) -> eval(E, ID) end, Elems);

eval({tuple, Left, Right}, ID) ->
  LeftV = eval(Left, ID),
  RightV = eval(Right, ID),
  {LeftV, RightV};

eval({map, Pairs}, ID) ->
  List = lists:map(fun({K, V}) ->
    {eval(K, ID), eval(V, ID)}
  end, Pairs),
  maps:from_list(List);

eval({var, _, Name}, ID) ->
  case env_get(Name, ID) of
    {lazy, Expr} ->
      V = eval(Expr, ID),
      env_update(Name, V, ID),
      V;
    {lazy_pattern, Pattern, Expr, PatternNames} ->
      V = eval(Expr, ID),
      lists:foreach(fun(PatternName) ->
        env_set(PatternName, {}, ID)
      end, PatternNames),

      case match(V, Pattern, ID) of
        false -> error({badmatch, V, Pattern});
        true -> env_get(Name, ID)
      end;
    {struct, _, V} -> V;
    V -> V
  end;

eval({con_var, Line, Name}, ID) -> eval({var, Line, Name}, ID);

eval({record, {con_var, _, Name}, Inits}, ID) ->
  {struct, FieldNames, Fn} = env_get(Name, ID),

  Vs = lists:map(fun(FieldName) ->
    {_, Expr} = hd(lists:filter(fun({{var, _, InitName}, _}) ->
      FieldName == InitName
    end, Inits)),
    eval(Expr, ID)
  end, FieldNames),

  Fn(Vs);

eval({app, Expr, Args}, ID) ->
  Fn = eval(Expr, ID),
  Vs = if
    length(Args) == 0 -> [none];
    true -> lists:map(fun(Arg) -> eval(Arg, ID) end, Args)
  end,
  Fn(Vs);

eval({native, {atom, _, Module}, {var, _, Name}, Arity}, _) ->
  Fn = list_to_atom(Name),
  curry_native(fun Module:Fn/Arity);

eval({{'if', _}, Expr, Then, Else}, ID) ->
  V = case eval(Expr, ID) of
    true -> eval(Then, ID);
    false -> eval(Else, ID)
  end,
  case Else of
    none -> none;
    _ -> V
  end;

eval({{'let', _}, Inits, Expr}, ID) ->
  InitNames = lists:map(fun({Pattern, _}) ->
    gb_sets:to_list(par:pattern_names(Pattern))
  end, Inits),
  InitsWithNames = lists:zip(Inits, InitNames),

  ChildID = env_create_child(ID),
  lists:foreach(fun({{Pattern, InitExpr}, Names}) ->
    lists:foreach(fun(Name) ->
      Value = {lazy_pattern, Pattern, InitExpr, Names},
      env_set(Name, Value, ChildID)
    end, Names)
  end, InitsWithNames),

  lists:foreach(fun({{Pattern, InitExpr}, Names}) ->
    V = eval(InitExpr, ChildID),
    lists:foreach(fun(Name) ->
      env_set(Name, {}, ChildID)
    end, Names),

    case match(V, Pattern, ChildID) of
      false -> error({badmatch, V, Pattern});
      true -> true
    end
  end, InitsWithNames),

  eval(Expr, ChildID);

eval({{'match', _}, Expr, Cases}, ID) ->
  V = eval(Expr, ID),
  match_cases(V, Cases, ID);

eval({block, Exprs}, ID) ->
  lists:foldl(fun(Expr, _) -> eval(Expr, ID) end, none, Exprs);

eval({{Op, _}, Left, Right}, ID) ->
  LeftV = eval(Left, ID),
  RightV = eval(Right, ID),

  case Op of
    '==' -> LeftV == RightV;
    '!=' -> LeftV /= RightV;
    '||' -> LeftV or RightV;
    '&&' -> LeftV and RightV;
    '>' -> LeftV > RightV;
    '<' -> LeftV < RightV;
    '>=' -> LeftV >= RightV;
    '<=' -> LeftV =< RightV;
    '+' -> LeftV + RightV;
    '-' -> LeftV - RightV;
    '*' -> LeftV * RightV;
    '/' -> LeftV / RightV;
    '%' -> LeftV rem RightV;
    '++' ->
      if
        is_binary(LeftV) -> <<LeftV/binary, RightV/binary>>;
        is_list(LeftV) -> LeftV ++ RightV;
        is_map(LeftV) -> maps:merge(LeftV, RightV);
        true ->
          true = gb_sets:is_set(LeftV),
          gb_sets:union(LeftV, RightV)
      end;
    '--' ->
      if
        is_list(LeftV) ->
          Set = gb_sets:from_list(RightV),
          lists:filter(fun(Elem) ->
            not gb_sets:is_member(Elem, Set)
          end, LeftV);
        true ->
          true = gb_sets:is_set(LeftV),
          gb_sets:subtract(LeftV, RightV)
      end
  end;

eval({{Op, _}, Expr}, ID) ->
  V = eval(Expr, ID),

  case Op of
    '!' -> not V;
    '#' -> gb_sets:from_list(V);
    '-' -> -V;
    'discard' -> none
  end.

curry(Arity, Callback, ArgVs) ->
  fun(Action) ->
    case Action of
      uncurry ->
        uncurry(Arity - length(ArgVs), fun(NewVs) ->
          Callback(ArgVs ++ NewVs)
        end);

      NewVs when is_list(NewVs) ->
        Vs = ArgVs ++ NewVs,

        if
          Arity == 0 ->
            [none | Rest] = Vs,
            Result = Callback([none]),
            if
              is_function(Result) and (length(Rest) > 0) -> Result(Rest);
              true -> Result
            end;

          length(Vs) >= Arity ->
            {AppVs, Rest} = if
              length(Vs) > Arity -> lists:split(Arity, Vs);
              true -> {Vs, []}
            end,

            Result = Callback(AppVs),
            if
              is_function(Result) and (length(Rest) > 0) -> Result(Rest);
              true -> Result
            end;

          true -> curry(Arity, Callback, Vs)
        end
    end
  end.

curry_native(Fun) ->
  {arity, Arity} = erlang:fun_info(Fun, arity),
  curry(Arity, fun(Vs) ->
    Result = if
      Arity == 0 -> Fun();
      true ->
        NativeVs = lists:map(fun(V) ->
          if is_function(V) -> V(uncurry); true -> V end
        end, Vs),
        apply(Fun, NativeVs)
    end,

    if is_function(Result) -> curry_native(Result); true -> Result end
  end, []).

uncurry(Arity, Callback) ->
  % As far as I know, there's no way to create a function with a dynamic number
  % of arguments, so we do it manually up to 10 (a guessed maximum) here.
  case Arity of
    0 -> fun() ->
      Callback([none])
    end;
    1 -> fun(A) ->
      Callback([A])
    end;
    2 -> fun(A, B) ->
      Callback([A, B])
    end;
    3 -> fun(A, B, C) ->
      Callback([A, B, C])
    end;
    4 -> fun(A, B, C, D) ->
      Callback([A, B, C, D])
    end;
    5 -> fun(A, B, C, D, E) ->
      Callback([A, B, C, D, E])
    end;
    6 -> fun(A, B, C, D, E, F) ->
      Callback([A, B, C, D, E, F])
    end;
    7 -> fun(A, B, C, D, E, F, G) ->
      Callback([A, B, C, D, E, F, G])
    end;
    8 -> fun(A, B, C, D, E, F, G, H) ->
      Callback([A, B, C, D, E, F, G, H])
    end;
    9 -> fun(A, B, C, D, E, F, G, H, I) ->
      Callback([A, B, C, D, E, F, G, H, I])
    end;
    10 -> fun(A, B, C, D, E, F, G, H, I, J) ->
      Callback([A, B, C, D, E, F, G, H, I, J])
    end
  end.

match_cases(V, [], _) -> error({badmatch, V});
match_cases(V, [{Pattern, Expr} | Rest], ID) ->
  % TODO: stop all new_childs
  ChildID = env_create_child(ID),
  lists:foreach(fun(Name) ->
    env_set(Name, {}, ChildID)
  end, gb_sets:to_list(par:pattern_names(Pattern))),

  case match(V, Pattern, ChildID) of
    true -> eval(Expr, ChildID);
    false -> match_cases(V, Rest, ID)
  end.

match(V1, {N, _, V2}, _)
  when N == int; N == float; N == bool; N == str; N == atom -> V1 == V2;

match(V1, {var, _, Name}, ID) ->
  case env_get(Name, ID) of
    {} ->
      env_set(Name, V1, ID),
      true;
    V2 -> {V1 == V2}
  end;

match(V1, {var_value, Line, Name}, ID) -> V1 == eval({var, Line, Name}, ID);
match(_, {'_', _}, _) -> true;

match(V1, {con_var, _, Name}, ID) ->
  case env_get(Name, ID) of
    % can't match functions
    {struct, _, _} -> false;
    V2 when not is_function(V2) -> V1 == V2;
    _ -> false
  end;

match(V, {app, {con_var, Line, Name}, Args}, ID) ->
  Atom = list_to_atom(Name),
  if
    length(Args) == 0 -> V == Atom;
    true ->
      match(tuple_to_list(V), {list, [{atom, Line, Atom} | Args]}, ID)
  end;

match(V, {list, List}, ID) ->
  if
    length(V) /= length(List) -> false;
    true ->
      lists:foldl(fun({ExpV, Elem}, Matched) ->
        case Matched of
          false -> false;
          true -> match(ExpV, Elem, ID)
        end
      end, true, lists:zip(V, List))
  end;

match(V, {list, List, Rest}, ID) ->
  if
    length(V) < length(List) -> false;
    true ->
      SubV = lists:sublist(V, length(List)),
      RestV = lists:sublist(V, length(List) + 1, length(V)),

      case match(SubV, {list, List}, ID) of
        false -> false;
        true -> match(RestV, Rest, ID)
      end
  end;

match(V, {tuple, Left, Right}, ID) ->
  match(tuple_to_list(V), {list, [Left, Right]}, ID).

env_create_first() ->
  case ets:info(envs) of
    undefined -> true;
    _ -> ets:delete(envs)
  end,
  ets:new(envs, [set, named_table]),
  ets:insert(envs, [{next_id, 2}, {1, #{}, undefined}]),
  1.

env_create_child(ParentID) ->
  ID = ets:lookup_element(envs, next_id, 2),
  ets:insert(envs, [{next_id, ID + 1}, {ID, #{}, ParentID}]),
  ID.

env_get(Name, ID) ->
  [{_, Env, ParentID}] = ets:lookup(envs, ID),
  case maps:find(Name, Env) of
    {ok, Value} -> Value;
    error ->
      case ParentID of
        undefined -> error({badkey, Name});
        _ -> env_get(Name, ParentID)
      end
  end.

env_set(Name, Value, ID) ->
  [{_, Env, ParentID}] = ets:lookup(envs, ID),
  ets:insert(envs, {ID, Env#{Name => Value}, ParentID}).

env_update(Name, Value, ID) ->
  [{_, Env, ParentID}] = ets:lookup(envs, ID),
  case maps:find(Name, Env) of
    {ok, _} -> ets:insert(envs, {ID, Env#{Name => Value}, ParentID});
    error ->
      case ParentID of
        undefined -> error({badkey, Name});
        _ -> env_update(Name, Value, ParentID)
      end
  end.
