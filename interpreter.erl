-module(interpreter).
-export([reload/1, execute/1]).

reload(Syntax) ->
  par:reload(Syntax),

  code:purge(?MODULE),
  {ok, _} = compile:file(?MODULE),
  code:load_file(?MODULE).

execute(Ast) ->
  {ok, Pid} = global_env_server:start_link(),
  lists:foreach(fun(Node) -> update_global_env(Node, Pid) end, Ast),

  lists:foreach(fun(Node) ->
    case Node of
      % strictly evaluate all global variables except functions
      {global, Var, Expr} when element(1, Expr) /= fn -> eval(Var, #{}, Pid);
      _ -> true
    end
  end, Ast),

  eval({app, {var, 0, "main"}, []}, #{}, Pid).

update_global_env({global, {var, _, Name}, Expr}, Pid) ->
  global_env_server:set(Name, {lazy, Expr}, Pid);

update_global_env({enum, _, OptionTEs}, Pid) ->
  lists:foreach(fun({option, {con_token, _, Name}, ArgsTE}) ->
    Value = if
      length(ArgsTE) == 0 -> list_to_atom(Name);
      true ->
        curry(length(ArgsTE), fun(Vs) ->
          list_to_tuple([list_to_atom(Name) | Vs])
        end, [])
    end,

    global_env_server:set(Name, Value, Pid)
  end, OptionTEs);

update_global_env({struct, StructTE, FieldTEs}, Pid) ->
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

  global_env_server:set(StructName, {struct, FieldNames, Value}, Pid);

update_global_env({sig, _, _}, _) -> true.

eval({fn, Args, Expr}, Env, Pid) ->
  curry(length(Args), fun(Vs) ->
    NewEnv = if
      length(Args) == 0 -> Env;
      true ->
        lists:foldl(fun({{var, _, Name}, V}, FoldEnv) ->
          FoldEnv#{Name => V}
        end, Env, lists:zip(Args, Vs))
    end,

    eval(Expr, NewEnv, Pid)
  end, []);

eval({expr_sig, Expr, _}, Env, Pid) -> eval(Expr, Env, Pid);

eval(none, _, _) -> none;
eval({int, _, V}, _, _) -> V;
eval({float, _, V}, _, _) -> V;
eval({bool, _, V}, _, _) -> V;
eval({str, _, V}, _, _) -> V;
eval({atom, _, V}, _, _) -> V;

eval({list, Elems}, Env, Pid) ->
  lists:map(fun(E) -> eval(E, Env, Pid) end, Elems);

eval({tuple, Elems}, Env, Pid) ->
  list_to_tuple(eval({list, Elems}, Env, Pid));

eval({map, Pairs}, Env, Pid) ->
  List = lists:map(fun({K, V}) ->
    {eval(K, Env, Pid), eval(V, Env, Pid)}
  end, Pairs),
  maps:from_list(List);

eval({var, _, Name}, Env, Pid) ->
  case maps:find(Name, Env) of
    {ok, V} -> V;
    error ->
      case global_env_server:get(Name, Pid) of
        {lazy, Expr} ->
          V = eval(Expr, Env, Pid),
          global_env_server:set(Name, V, Pid),
          V;
        {struct, _, V} -> V;
        V -> V
      end
  end;

eval({record, {var, _, Name}, Inits}, Env, Pid) ->
  {struct, FieldNames, Fn} = global_env_server:get(Name, Pid),

  Vs = lists:map(fun(FieldName) ->
    {_, Expr} = hd(lists:filter(fun({{var, _, InitName}, _}) ->
      FieldName == InitName
    end, Inits)),
    eval(Expr, Env, Pid)
  end, FieldNames),

  Fn(Vs);

eval({app, Expr, Args}, Env, Pid) ->
  Fn = eval(Expr, Env, Pid),
  Vs = if
    length(Args) == 0 -> [none];
    true -> lists:map(fun(Arg) -> eval(Arg, Env, Pid) end, Args)
  end,
  Fn(Vs);

eval({native, {atom, _, Module}, {var, _, Name}, Arity}, _, _) ->
  Fn = list_to_atom(Name),
  curry_native(fun Module:Fn/Arity);

eval({{'if', _}, Expr, Then, Else}, Env, Pid) ->
  Result = case eval(Expr, Env, Pid) of
    true -> eval(Then, Env, Pid);
    false -> eval(Else, Env, Pid)
  end,
  case Else of
    none -> none;
    _ -> Result
  end;

eval({{'let', _}, Inits, Expr}, Env, Pid) ->
  NewEnv = lists:foldl(fun({{var, _, Name}, InitExpr}, FoldEnv) ->
    V = eval(InitExpr, FoldEnv, Pid),
    FoldEnv#{Name => V}
  end, Env, Inits),

  eval(Expr, NewEnv, Pid);

eval({block, Exprs}, Env, Pid) ->
  lists:foldl(fun(Expr, _) -> eval(Expr, Env, Pid) end, none, Exprs);

eval({{Op, _}, Left, Right}, Env, Pid) ->
  LeftV = eval(Left, Env, Pid),
  RightV = eval(Right, Env, Pid),

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

eval({{Op, _}, Expr}, Env, Pid) ->
  V = eval(Expr, Env, Pid),

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
