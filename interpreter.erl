-module(interpreter).
-export([reload/1, execute/1]).

reload(Syntax) ->
  par:reload(Syntax),

  code:purge(?MODULE),
  {ok, _} = compile:file(?MODULE),
  code:load_file(?MODULE).

execute(Ast) ->
  Env = lists:foldl(fun(Node, Env) ->
    case Node of
      {fn, {var, _, Name}, _, _} ->
        Env#{Name => {lazy, Node}};
      _ -> Env
    end
  end, #{}, Ast),

  #{"main" := {lazy, Expr}} = Env,
  Main = eval(Expr, Env),
  Main([]).

eval({fn, Var, Args, Expr}, Env) ->
  fun(Vs) ->
    case Vs of
      unwrap ->
        % When passing callbacks to native functions, we need to unwrap them so
        % they're explicit in their argument list, as opposed to taking
        % a variable-length array of curried arguments. The caller is asking
        % this function to unwrap itself.
        unwrap({fn, Var, Args, Expr}, Env);

      _ ->
        {AppVs, LeftVs} = if
          length(Vs) > length(Args) -> lists:split(length(Args), Vs);
          true -> {Vs, []}
        end,

        {LeftArgs, NewEnv} = lists:foldl(fun(V, {FoldArgs, FoldEnv}) ->
          {var, _, Name} = hd(FoldArgs),
          {tl(FoldArgs), FoldEnv#{Name => V}}
        end, {Args, Env}, AppVs),

        case length(LeftArgs) of
          0 ->
            Result = eval(Expr, NewEnv),
            if length(LeftVs) > 0 -> Result(LeftVs); true -> Result end;
          _ -> eval({fn, Var, LeftArgs, Expr}, NewEnv)
        end
    end
  end;

eval({expr_sig, Expr, _}, Env) -> eval(Expr, Env);

eval({int, _, V}, _) -> V;
eval({float, _, V}, _) -> V;
eval({bool, _, V}, _) -> V;
eval({str, _, V}, _) -> V;
eval({atom, _, V}, _) -> V;

eval({list, Elems}, Env) ->
  lists:map(fun(E) -> eval(E, Env) end, Elems);

eval({tuple, Elems}, Env) ->
  list_to_tuple(eval({list, Elems}, Env));

eval({map, Pairs}, Env) ->
  List = lists:map(fun({K, V}) -> {eval(K, Env), eval(V, Env)} end, Pairs),
  maps:from_list(List);

eval({var, _, Name}, Env) ->
  case maps:get(Name, Env) of
    {lazy, Expr} -> eval(Expr, Env);
    V -> V
  end;

eval({app, Expr, Args}, Env) ->
  Fn = eval(Expr, Env),
  Vs = lists:map(fun(Arg) -> eval(Arg, Env) end, Args),
  Fn(Vs);

eval({native, {atom, _, Module}, {var, _, Name}, Arity}, _) ->
  Fn = list_to_atom(Name),
  wrap(fun Module:Fn/Arity, []);

eval({{'let', _}, Inits, Expr}, Env) ->
  NewEnv = lists:foldl(fun({{var, _, Name}, InitExpr}, FoldEnv) ->
    V = eval(InitExpr, FoldEnv),
    FoldEnv#{Name => V}
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

unwrap({fn, _, Args, Expr}, Env) ->
  % As far as I know, there's no way to create a function with a dynamic number
  % of arguments, so we do it manually up to 10 (a guessed maximum) here.
  case length(Args) of
    1 -> fun(A) ->
      unwrap_eval(Args, [A], Expr, Env)
    end;
    2 -> fun(A, B) ->
      unwrap_eval(Args, [A, B], Expr, Env)
    end;
    3 -> fun(A, B, C) ->
      unwrap_eval(Args, [A, B, C], Expr, Env)
    end;
    4 -> fun(A, B, C, D) ->
      unwrap_eval(Args, [A, B, C, D], Expr, Env)
    end;
    5 -> fun(A, B, C, D, E) ->
      unwrap_eval(Args, [A, B, C, D, E], Expr, Env)
    end;
    6 -> fun(A, B, C, D, E, F) ->
      unwrap_eval(Args, [A, B, C, D, E, F], Expr, Env)
    end;
    7 -> fun(A, B, C, D, E, F, G) ->
      unwrap_eval(Args, [A, B, C, D, E, F, G], Expr, Env)
    end;
    8 -> fun(A, B, C, D, E, F, G, H) ->
      unwrap_eval(Args, [A, B, C, D, E, F, G, H], Expr, Env)
    end;
    9 -> fun(A, B, C, D, E, F, G, H, I) ->
      unwrap_eval(Args, [A, B, C, D, E, F, G, H, I], Expr, Env)
    end;
    10 -> fun(A, B, C, D, E, F, G, H, I, J) ->
      unwrap_eval(Args, [A, B, C, D, E, F, G, H, I, J], Expr, Env)
    end
  end.

unwrap_eval(Args, Vs, Expr, Env) ->
  NewEnv = lists:foldl(fun({{var, _, Name}, V}, FoldEnv) ->
    FoldEnv#{Name => V}
  end, Env, lists:zip(Args, Vs)),

  eval(Expr, NewEnv).

wrap(Fun, SavedVs) ->
  {arity, Arity} = erlang:fun_info(Fun, arity),
  fun(NewVs) ->
    case NewVs of
      unwrap ->
        % When passing callbacks to native functions, we need to unwrap them so
        % they're explicit in their argument list, as opposed to taking
        % a variable-length array of curried arguments. The caller is asking
        % this function to unwrap itself.
        Fun;

      _ ->
        Vs = SavedVs ++ NewVs,
        if
          length(Vs) >= Arity ->
            {AppVs, LeftVs} = if
              length(Vs) > Arity -> lists:split(Arity, Vs);
              true -> {Vs, []}
            end,

            NativeVs = lists:map(fun(V) ->
              if is_function(V) -> V(unwrap); true -> V end
            end, AppVs),

            Raw = apply(Fun, NativeVs),
            Result = if is_function(Raw) -> wrap(Raw, []); true -> Raw end,
            if length(LeftVs) > 0 -> Result(LeftVs); true -> Result end;
          true -> wrap(Fun, Vs)
        end
    end
  end.
