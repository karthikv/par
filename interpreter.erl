-module(interpreter).
-export([reload/1, execute/1]).

reload(LexParse) ->
  par:reload(LexParse),

  code:purge(?MODULE),
  {ok, _} = compile:file(?MODULE),
  code:load_file(?MODULE).

execute(Ast) ->
  Env = lists:foldl(fun(Node, Env) ->
    case Node of
      {fn, {var, _, Name}, _, _} ->
        dict:store(Name, {lazy, Node}, Env);
      _ -> Env
    end
  end, dict:new(), Ast),

  {lazy, Expr} = dict:fetch("main", Env),
  Main = eval(Expr, Env),
  Main([]).

eval({fn, Var, Args, Expr}, Env) ->
  fun(Vs) ->
    {LeftArgs, NewEnv} = lists:foldl(fun(V, {FoldArgs, FoldEnv}) ->
      {var, _, Name} = hd(FoldArgs),
      {tl(FoldArgs), dict:store(Name, V, FoldEnv)}
    end, {Args, Env}, Vs),

    case length(LeftArgs) of
      0 -> eval(Expr, NewEnv);
      _ -> eval({fn, Var, LeftArgs, Expr}, NewEnv)
    end
  end;

eval({expr_sig, Expr, _}, Env) -> eval(Expr, Env);

eval({int, _, V}, _) -> V;
eval({float, _, V}, _) -> V;
eval({bool, _, V}, _) -> V;
eval({str, _, V}, _) -> V;

eval({list, Elems}, Env) ->
  lists:map(fun(E) -> eval(E, Env) end, Elems);

eval({tuple, Elems}, Env) ->
  list_to_tuple(eval({list, Elems}, Env));

eval({map, Pairs}, Env) ->
  List = lists:map(fun({K, V}) -> {eval(K, Env), eval(V, Env)} end, Pairs),
  maps:from_list(List);

eval({var, _, Name}, Env) ->
  case dict:fetch(Name, Env) of
    {lazy, Expr} -> eval(Expr, Env);
    V -> V
  end;

eval({app, Expr, Args}, Env) ->
  Fn = eval(Expr, Env),
  Vs = lists:map(fun(Arg) -> eval(Arg, Env) end, Args),
  Fn(Vs);

eval({{'let', _}, Inits, Expr}, Env) ->
  NewEnv = lists:foldl(fun({{var, _, Name}, InitExpr}, FoldEnv) ->
    V = eval(InitExpr, FoldEnv),
    dict:store(Name, V, FoldEnv)
  end, Env, Inits),

  eval(Expr, NewEnv);

eval({{'if', _}, Expr, Then, Else}, Env) ->
  case eval(Expr, Env) of
    true -> eval(Then, Env);
    false -> eval(Else, Env)
  end;

eval({{Op, _}, Left, Right}, Env) ->
  LeftV = eval(Left, Env),
  RightV = eval(Right, Env),

  case Op of
    '==' -> LeftV == RightV;
    '!=' -> LeftV =/= RightV;
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

eval({{Op, _}, Expr}, Env) ->
  V = eval(Expr, Env),

  case Op of
    '!' -> not V;
    '#' -> gb_sets:from_list(V);
    '-' -> -V
  end.
