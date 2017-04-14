-module(par).
-import(lexer, [string/1]).
-import(parser, [parse/1]).
-export([main/1, fresh/1]).

-record(ctx, {csts, env, count}).
csts(C) -> C#ctx.csts.
env(C) -> C#ctx.env.
count(C) -> C#ctx.count.

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
  {ok, Tokens, _} = lexer:string("add(a, b) = a + b  main() = add(3, 5)"),
  {ok, Ast} = parser:parse(Tokens),
  io:format("AST: ~p~n", [Ast]),

  {_, C} = infer(Ast, #ctx{csts=[], env=dict:new(), count=0}),
  io:format("csts: ~p~n", [csts(C)]),

  case solve(csts(C), dict:new(), []) of
    {ok, Subs} -> io:format("soln: ~p~n", [dict:to_list(Subs)]);
    {errors, Errs} -> io:format("type errors: ~p~n", [Errs])
  end.

infer([A|B], C) ->
  {_, C1} = infer(A, C),
  infer(B, C1);

infer([], C) -> {[], C};

infer({fn, {var, _, Name}, Args, Expr}, C) ->
  {ArgsT, C1} = lists:foldr(fun({var, _, ArgName}, {Ts, FoldC}) ->
    {TV, FoldC1} = fresh(FoldC),
    {[TV|Ts], FoldC1#ctx{
      env=dict:store(ArgName, {gb_sets:new(), TV}, env(FoldC1))}
    }
  end, {[], C}, Args),

  {ReturnT, C2} = infer(Expr, C1),
  T = lists:foldr(fun(ArgT, LastT) -> {lam, ArgT, LastT} end, ReturnT, ArgsT),
  {T, C2#ctx{
    % use C to avoid bringing in env from arguments
    env=dict:store(Name, generalize(T, C), env(C))
  }};

infer({int, _, _}, C) -> {{con, int}, C};
infer({bool, _, _}, C) -> {{con, bool}, C};
infer({var, _, Name}, C) -> lookup(Name, C);

infer({app, Var, Args}, C) ->
  {ArgsT, C1} = lists:foldr(fun(Arg, {Ts, FoldC}) ->
    {T, FoldC1} = infer(Arg, FoldC),
    {[T|Ts], FoldC1}
  end, {[], C}, Args),

  {VarT, C2} = infer(Var, C1),
  {TV, C3} = fresh(C2),
  T = lists:foldr(fun(ArgT, LastT) -> {lam, ArgT, LastT} end, TV, ArgsT),
  {TV, C3#ctx{csts=[{T, VarT}|csts(C3)]}};

infer({{'+', _}, Left, Right}, C) ->
  {LeftT, C1} = infer(Left, C),
  {RightT, C2} = infer(Right, C1),
  {TV, C3} = fresh(C2),
  Cst = {
    {lam, LeftT, {lam, RightT, TV}},
    {lam, {con, int}, {lam, {con, int}, {con, int}}}
  },
  {TV, C3#ctx{csts=[Cst|csts(C3)]}}.

lookup(Name, C) ->
  {ok, {GTVs, T}} = dict:find(Name, env(C)),
  {Subs, C1} = gb_sets:fold(fun(GTV, {D, FoldC}) ->
    {NewTV, FoldC1} = fresh(FoldC),
    {dict:store(GTV, NewTV, D), FoldC1}
  end, {dict:new(), C}, GTVs),
  {subs(T, Subs), C1}.

solve([{L, R}|Rest], Subs1, Errs1) ->
  case unify({subs(L, Subs1), subs(R, Subs1)}) of
    {ok, Subs2} -> solve(Rest, merge_subs(Subs1, Subs2), Errs1);
    {errors, Errs2} -> solve(Rest, Subs1, Errs1 ++ Errs2)
  end;
solve([], _, Errs) when length(Errs) > 0 -> {errors, Errs};
solve([], Subs, _) -> {ok, Subs}.

unify({T1, T2}) when T1 == T2 -> {ok, dict:new()};
unify({{lam, ArgsT1, ReturnT1}, {lam, ArgsT2, ReturnT2}}) ->
  case unify({ArgsT1, ArgsT2}) of
    {ok, Subs1} ->
      case unify({subs(ReturnT1, Subs1), subs(ReturnT2, Subs1)}) of
        {ok, Subs2} -> {ok, merge_subs(Subs1, Subs2)};
        {errors, Errs} -> {errors, Errs}
      end;
    {errors, Errs1} ->
      case unify({ReturnT1, ReturnT2}) of
        {ok, _} -> {errors, Errs1};
        {errors, Errs2} -> {errors, Errs1 ++ Errs2}
      end
 end;
unify({{tv, TV}, T}) ->
  Occurs = occurs(TV, T),
  if Occurs -> {errors, [{{tv, TV}, T}]};
     true -> {ok, dict:from_list([{TV, T}])}
  end;
unify({T, {tv, TV}}) ->
  Occurs = occurs(TV, T),
  if Occurs -> {errors, [{{tv, TV}, T}]};
     true -> {ok, dict:from_list([{TV, T}])}
  end;
unify({T1, T2}) -> {errors, [{T1, T2}]}.

subs({lam, ArgsT, ReturnT}, Subs) ->
  {lam, subs(ArgsT, Subs), subs(ReturnT, Subs)};
subs({tv, TV}, Subs) ->
  case dict:find(TV, Subs) of
    {ok, TSub} -> TSub;
    error -> {tv, TV}
  end;
subs({con, T}, _) -> {con, T}.

merge_subs(Subs1, Subs2) ->
  dict:merge(fun(K, V1, V2) ->
    error({badarg, K}, [K, V1, V2])
  end, Subs1, Subs2).

generalize(T, C) ->
  EnvFTVs = dict:fold(fun(_, {GTVs, EnvT}, S) ->
    gb_sets:union(S, gb_sets:subtract(ftvs(EnvT), GTVs))
  end, gb_sets:new(), env(C)),
  GTVs = gb_sets:subtract(ftvs(T), EnvFTVs),
  {GTVs, T}.

ftvs({lam, ArgsT, ReturnT}) -> gb_sets:union(ftvs(ArgsT), ftvs(ReturnT));
ftvs({tv, TV}) -> gb_sets:from_list([TV]);
ftvs({con, _}) -> gb_sets:new().

occurs(TV1, {tv, TV2}) when TV1 == TV2 -> true;
occurs(TV, {lam, ArgsT, ReturnT}) ->
  occurs(TV, ArgsT) or occurs(TV, ReturnT);
occurs(_, _) -> false.

fresh(C) -> {{tv, gen_name(count(C))}, C#ctx{count=count(C) + 1}}.

gen_name(Count) when Count < 26 -> [$A + Count];
gen_name(Count) -> [$A + (Count rem 26)|gen_name(Count - 26)].
