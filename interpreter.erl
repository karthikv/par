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
      {global, {var, _, Name}, Expr} ->
        Env#{Name => {lazy, Expr}};
      _ -> Env
    end
  end, #{}, Ast),

  #{"main" := {lazy, Expr}} = Env,
  Main = eval(Expr, Env),
  Main([none]).

eval({fn, Args, Expr}, Env) ->
  curry(length(Args), fun(Vs) ->
    NewEnv = if
      length(Args) == 0 -> Env;
      true ->
        lists:foldl(fun({{var, _, Name}, V}, FoldEnv) ->
          FoldEnv#{Name => V}
        end, Env, lists:zip(Args, Vs))
    end,

    eval(Expr, NewEnv)
  end, []);

eval({expr_sig, Expr, _}, Env) -> eval(Expr, Env);

eval(none, _) -> none;
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
  Vs = if
    length(Args) == 0 -> [none];
    true -> lists:map(fun(Arg) -> eval(Arg, Env) end, Args)
  end,
  Fn(Vs);

eval({native, {atom, _, Module}, {var, _, Name}, Arity}, _) ->
  Fn = list_to_atom(Name),
  curry_native(fun Module:Fn/Arity);

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
