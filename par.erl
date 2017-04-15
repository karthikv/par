-module(par).
-import(lexer, [string/1]).
-import(parser, [parse/1]).
-export([main/1]).

-record(ctx, {csts, env, pid, deps}).
-record(solver, {subs, errs, pid}).

% Naming conventions:
% TV - type variable
% fresh - a function that generates a new TV
% FTV - free type variable; a TV that hasn't yet been generalized
% ftvs - a function that computes a set of FTVs in an expression
% T - type; can be a concrete type like int, a TV, or a function type encoded
%     as an array
% Scheme - scheme; a tuple {GTVs, T} that represents a T generalized across
%          GTVs, a set of TVs
% C - context record with the following fields:
%   csts - array of constraints, each constraint is an array of two Ts that
%          must match
%   env - dict mapping variable name to Scheme
%   count - a monotonically increasing count used to generate fresh TVs

main(["lex"]) ->
  {ok, Path} = leex:file("lexer.xrl"),
  compile:file(Path),
  io:format("~p~n", [Path]);

main(["parse"]) ->
  {ok, Path} = yecc:file("parser.yrl"),
  compile:file(Path),
  io:format("~p~n", [Path]);

main([]) ->
  {ok, Tokens, _} = lexer:string("cmp(f, g, x) = f(g(x))  p5(x) = x + 5  p3(x) = x + 3  main() = cmp(p3, p5, 1)"),
  {ok, Ast} = parser:parse(Tokens),
  io:format("AST: ~p~n", [Ast]),

  {ok, Pid} = tv_server:start_link(),
  C = lists:foldl(fun({fn, {var, _, Name}, _, _}, C) ->
    % TODO: what if name already exists?
    TV = tv_server:fresh(C#ctx.pid),
    C#ctx{env=dict:store(Name, {fn, TV}, C#ctx.env)}
  end, #ctx{csts=[], env=dict:new(), pid=Pid, deps=[]}, Ast),

  {FCs, C1} = lists:foldl(fun(Node, {FCs, FoldC}) ->
    {TV, FoldC1} = infer(Node, FoldC#ctx{csts=[], deps=[]}),
    {[{TV, FoldC1}|FCs], FoldC1}
  end, {[], C}, Ast),

  case solve(FCs, #solver{subs=dict:new(), errs=[], pid=Pid}) of
    {ok, Subs} ->
      io:format("soln: ~p~n", [dict:to_list(Subs)]),
      lists:foreach(fun({Name, {_, T}}) ->
        io:format("type ~p = ~s~n", [Name, pretty(subs(T, Subs))])
      end, dict:to_list(C1#ctx.env));
    {errors, Errs} -> io:format("type errors: ~p~n", [Errs])
  end.

pretty({lam, ArgsT, ReturnT}) ->
  Format = case ArgsT of
    {lam, _, _} -> "(~s) -> ~s";
    _ -> "~s -> ~s"
  end,
  io_lib:format(Format, [pretty(ArgsT), pretty(ReturnT)]);
pretty({tv, TV}) -> io_lib:format("~p", [TV]);
pretty({con, T}) -> io_lib:format("~p", [T]).

infer({fn, {var, _, Name}, Args, Expr}, C) ->
  {_, FnTV} = dict:fetch(Name, C#ctx.env),
  {ArgsT, C1} = lists:foldr(fun({var, _, ArgName}, {Ts, FoldC}) ->
    TV = tv_server:fresh(FoldC#ctx.pid),
    {[TV|Ts], FoldC#ctx{
      env=dict:store(ArgName, {arg, TV}, FoldC#ctx.env)
    }}
  end, {[], C}, Args),

  {ReturnT, C2} = infer(Expr, C1),
  T = lists:foldr(fun(ArgT, LastT) -> {lam, ArgT, LastT} end, ReturnT, ArgsT),
  io:format("deps ~p (~p) = ~p~n", [Name, FnTV, C2#ctx.deps]),
  {FnTV, C2#ctx{
    csts=[{FnTV, T}|C2#ctx.csts],
    % restore original env
    env=C#ctx.env
  }};

infer({int, _, _}, C) -> {{con, int}, C};
infer({bool, _, _}, C) -> {{con, bool}, C};
infer({var, _, Name}, C) ->
  % TODO: handle case where can't find variable
  {ok, {Type, T}} = dict:find(Name, C#ctx.env),
  Deps = if Type == fn -> [T|C#ctx.deps];
            true -> C#ctx.deps
         end,
  {{inst, T, C#ctx.env}, C#ctx{deps=Deps}};

infer({app, Var, Args}, C) ->
  {ArgsT, C1} = lists:foldr(fun(Arg, {Ts, FoldC}) ->
    {T, FoldC1} = infer(Arg, FoldC),
    {[T|Ts], FoldC1}
  end, {[], C}, Args),

  {VarT, C2} = infer(Var, C1),
  TV = tv_server:fresh(C2#ctx.pid),
  T = lists:foldr(fun(ArgT, LastT) -> {lam, ArgT, LastT} end, TV, ArgsT),
  {TV, C2#ctx{csts=[{T, VarT}|C2#ctx.csts]}};

infer({{'+', _}, Left, Right}, C) ->
  {LeftT, C1} = infer(Left, C),
  {RightT, C2} = infer(Right, C1),
  TV = tv_server:fresh(C2#ctx.pid),
  Cst = {
    {lam, LeftT, {lam, RightT, TV}},
    {lam, {con, int}, {lam, {con, int}, {con, int}}}
  },
  {TV, C2#ctx{csts=[Cst|C2#ctx.csts]}}.

solve([], #solver{errs=Errs}) when length(Errs) > 0 -> {errors, Errs};
solve([], #solver{subs=Subs}) -> {ok, Subs};
solve(FCs, S) ->
  {Solvable, Unsolved} = lists:partition(fun({_, C}) ->
    length(C#ctx.deps) == 0
  end, FCs),

  {Solved, S1} = lists:foldl(fun({TV, C}, {Solved, FoldS}) ->
    io:format("solving (~p) ~p~n", [TV, C#ctx.csts]),
    io:format("result: ~p~n", [unify_group(C#ctx.csts, FoldS)]),
    {gb_sets:add(TV, Solved), unify_group(C#ctx.csts, FoldS)}
  end, {gb_sets:new(), S}, Solvable),

  ToSolve = lists:map(fun({TV, C}) ->
    Deps = lists:filter(fun(Dep) ->
      not gb_sets:is_element(Dep, Solved)
    end, C#ctx.deps),
    {TV, C#ctx{deps=Deps}}
  end, Unsolved),

  solve(ToSolve, S1).

unify_group([], S) -> S;
unify_group([{L, R}|Rest], S) ->
  L1 = resolve(subs(L, S#solver.subs), S),
  R1 = resolve(subs(R, S#solver.subs), S),
  S1 = unify({L1, R1}, S),
  unify_group(Rest, S1).

resolve({lam, ArgsT, ReturnT}, S) ->
  {lam, resolve(ArgsT, S), resolve(ReturnT, S)};
resolve({tv, TV}, _) -> {tv, TV};
resolve({con, T}, _) -> {con, T};
resolve({inst, T, Env}, S) -> inst(generalize(T, Env), S).

inst({GTVs, T}, S) ->
  Subs = gb_sets:fold(fun(GTV, Subs) ->
    dict:store(GTV, tv_server:fresh(S#solver.pid), Subs)
  end, dict:new(), GTVs),
  subs(T, Subs).

generalize(T, Env) ->
  EnvFTVs = dict:fold(fun(_, {_, EnvT}, S) ->
    gb_sets:union(S, ftvs(EnvT))
  end, gb_sets:new(), Env),
  GTVs = gb_sets:subtract(ftvs(T), EnvFTVs),
  {GTVs, T}.

unify({T1, T2}, S) when T1 == T2 -> S;

unify({{lam, ArgsT1, ReturnT1}, {lam, ArgsT2, ReturnT2}}, S) ->
  S1 = unify({ArgsT1, ArgsT2}, S),
  ToUnify = {subs(ReturnT1, S1#solver.subs), subs(ReturnT2, S1#solver.subs)},
  unify(ToUnify, S1);
unify({{tv, TV}, T}, S) ->
  Occurs = occurs(TV, T),
  if Occurs -> S#solver{errs=[{{tv, TV}, T}|S#solver.errs]};
     true ->
       S#solver{subs=merge_subs(dict:from_list([{TV, T}]), S#solver.subs)}
  end;
unify({T, {tv, TV}}, S) ->
  Occurs = occurs(TV, T),
  if Occurs -> S#solver{errs=[{{tv, TV}, T}|S#solver.errs]};
     true ->
       S#solver{subs=merge_subs(dict:from_list([{TV, T}]), S#solver.subs)}
  end;
unify({T1, T2}, S) -> S#solver{errs=[{T1, T2}|S#solver.errs]}.

subs({lam, ArgsT, ReturnT}, Subs) ->
  {lam, subs(ArgsT, Subs), subs(ReturnT, Subs)};
subs({tv, TV}, Subs) ->
  case dict:find(TV, Subs) of
    {ok, TSub} -> subs(TSub, Subs);
    error -> {tv, TV}
  end;
subs({con, T}, _) -> {con, T};
subs({inst, T, Env}, Subs) -> {inst, subs(T, Subs), Env}.

merge_subs(Subs1, Subs2) ->
  dict:merge(fun(K, V1, V2) ->
    error({badarg, K}, [K, V1, V2])
  end, Subs1, Subs2).

ftvs({lam, ArgsT, ReturnT}) -> gb_sets:union(ftvs(ArgsT), ftvs(ReturnT));
ftvs({tv, TV}) -> gb_sets:from_list([TV]);
ftvs({con, _}) -> gb_sets:new();
% TODO: remove
ftvs({inst, T, _}) -> ftvs(T).

occurs(TV1, {tv, TV2}) when TV1 == TV2 -> true;
occurs(TV, {lam, ArgsT, ReturnT}) ->
  occurs(TV, ArgsT) or occurs(TV, ReturnT);
occurs(_, _) -> false.
