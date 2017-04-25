-module(par).
-export([reload/1, infer_prg/1]).

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
%
% TODO:
% - TODOs in code (non-unification error cases)
% - Type annotations
% - Error messages
% - Operation: nth element of tuple?
% - Data structures: sets, maps
% - Maybe else types (unit type?)
% - Complex types: ADTs
% - Typeclasses
% - Concurrency
% - Pattern matching
% - Extra type variables for return value of operators like == and +?
% - Better / Efficient EnvList
% - Codegen / Interpreter
% - Update naming conventions

reload(true) ->
  code:purge(lexer),
  {ok, _} = leex:file(lexer),
  {ok, _} = compile:file(lexer),
  code:load_file(lexer),

  code:purge(parser),
  {ok, _} = yecc:file(parser),
  {ok, _} = compile:file(parser),
  code:load_file(parser),

  reload(false);

reload(false) ->
  code:purge(tv_server),
  {ok, _} = compile:file(tv_server),
  code:load_file(tv_server),

  code:purge(?MODULE),
  {ok, _} = compile:file(?MODULE),
  code:load_file(?MODULE).

infer_prg(Prg) ->
  {ok, Tokens, _} = lexer:string(Prg),
  {ok, Ast} = parser:parse(Tokens),
  {ok, Pid} = tv_server:start_link(),

  C = lists:foldl(fun({fn, {var, _, Name}, _, _}, C) ->
    % TODO: what if name already exists?
    TV = tv_server:fresh(C#ctx.pid),
    C#ctx{env=dict:store(Name, {fn, TV}, C#ctx.env)}
  end, #ctx{csts=[], env=dict:new(), pid=Pid, deps=[]}, Ast),

  {FCs, C1} = lists:foldl(fun(Node, {FCs, FoldC}) ->
    {TV, FoldC1} = infer(Node, FoldC#ctx{csts=[], deps=[]}),
    {[{TV, FoldC1} | FCs], FoldC1}
  end, {[], C}, Ast),

  Result = case solve(FCs, #solver{subs=dict:new(), errs=[], pid=Pid}) of
    {ok, Subs} ->
      {ok, dict:map(fun(_, {_, T}) -> subs(T, Subs) end, C1#ctx.env)};
    {errors, Errs} -> {errors, Errs}
  end,

  ok = tv_server:stop(Pid),
  Result.

infer({fn, Var, Args, Expr}, C) ->
  {ArgsTRev, C1} = lists:foldl(fun({var, _, ArgName}, {Ts, FoldC}) ->
    TV = tv_server:fresh(FoldC#ctx.pid),
    {[TV | Ts], FoldC#ctx{
      env=dict:store(ArgName, {arg, TV}, FoldC#ctx.env)
    }}
  end, {[], C}, Args),

  {ReturnT, C2} = infer(Expr, C1),
  T = if length(Args) == 0 -> {lam, none, ReturnT};
         true -> lists:foldl(fun(ArgT, LastT) ->
           {lam, ArgT, LastT}
         end, ReturnT, ArgsTRev)
      end,

  case Var of
    {var, _, Name} ->
      {_, FnTV} = dict:fetch(Name, C#ctx.env),
      {FnTV, C2#ctx{
        csts=[{FnTV, T} | C2#ctx.csts],
        % restore original env
        env=C#ctx.env
      }};
    none ->
      % restore original env
      {T, C2#ctx{env=C#ctx.env}}
  end;

infer({int, _, _}, C) -> {tv_server:fresh_iface(num, C#ctx.pid), C};
infer({float, _, _}, C) -> {{con, float}, C};
infer({bool, _, _}, C) -> {{con, bool}, C};
infer({str, _, _}, C) -> {{gen, list, {con, char}}, C};
infer({list, Elems}, C) ->
  TV = tv_server:fresh(C#ctx.pid),
  {Csts, C1} = lists:foldl(fun(Elem, {FoldCsts, FoldC}) ->
    {ElemT, FoldC1} = infer(Elem, FoldC),
    {[{ElemT, TV} | FoldCsts], FoldC1}
  end, {[], C}, Elems),

  {{gen, list, TV}, C1#ctx{csts=Csts ++ C1#ctx.csts}};
infer({tuple, Elems}, C) ->
  {ElemsTRev, C1} = lists:foldl(fun(Elem, {FoldElemsT, FoldC}) ->
    {ElemT, FoldC1} = infer(Elem, FoldC),
    {[ElemT | FoldElemsT], FoldC1}
  end, {[], C}, Elems),

  T = lists:foldl(fun(ElemT, LastT) ->
    {tuple, ElemT, LastT}
  end, hd(ElemsTRev), tl(ElemsTRev)),
  {T, C1};

infer({var, _, Name}, C) ->
  % TODO: handle case where can't find variable
  {ok, {Type, T}} = dict:find(Name, C#ctx.env),
  Deps = case Type of
           fn -> [T | C#ctx.deps];
           _ -> C#ctx.deps
         end,
  {{inst, T, dict:to_list(C#ctx.env)}, C#ctx{deps=Deps}};

infer({app, Var, Args}, C) ->
  {ArgsTRev, C1} = lists:foldl(fun(Arg, {Ts, FoldC}) ->
    {T, FoldC1} = infer(Arg, FoldC),
    {[T | Ts], FoldC1}
  end, {[], C}, Args),

  {VarT, C2} = infer(Var, C1),
  TV = tv_server:fresh(C2#ctx.pid),
  T = lists:foldl(fun(ArgT, LastT) -> {lam, ArgT, LastT} end, TV, ArgsTRev),
  {TV, C2#ctx{csts=[{T, VarT} | C2#ctx.csts]}};

infer({{'let', _}, Inits, Expr}, C) ->
  C1 = lists:foldl(fun({{var, _, Name}, InitExpr}, FoldC) ->
    {T, FoldC1} = infer(InitExpr, FoldC),
    FoldC1#ctx{env=dict:store(Name, {'let', T}, FoldC1#ctx.env)}
  end, C, Inits),

  {T, C2} = infer(Expr, C1),
  {T, C2#ctx{env=C#ctx.env}};

infer({{'if', _}, Expr, Then, Else}, C) ->
  {ExprT, C1} = infer(Expr, C),
  {ThenT, C2} = infer(Then, C1),
  {ElseT, C3} = infer(Else, C2),

  TV = tv_server:fresh(C#ctx.pid),
  {TV, C3#ctx{
    csts=[{{con, bool}, ExprT}, {TV, ThenT}, {TV, ElseT} | C3#ctx.csts]}
  };

infer({{Op, _}, Left, Right}, C) ->
  {LeftT, C1} = infer(Left, C),
  {RightT, C2} = infer(Right, C1),

  TV = tv_server:fresh(C2#ctx.pid),

  Cst = if
    Op == '=='; Op == '!=' ->
      OperandTV = tv_server:fresh(C2#ctx.pid),
      {
        {lam, LeftT, {lam, RightT, TV}},
        {lam, OperandTV, {lam, OperandTV, {con, bool}}}
      };
    Op == '||'; Op == '&&' -> {
      {lam, LeftT, {lam, RightT, TV}},
      {lam, {con, bool}, {lam, {con, bool}, {con, bool}}}
    };
    Op == '>'; Op == '<'; Op == '>='; Op == '<=' ->
      NumTV = tv_server:fresh_iface(num, C2#ctx.pid),
      {
        {lam, LeftT, {lam, RightT, TV}},
        {lam, NumTV, {lam, NumTV, {con, bool}}}
      };
    Op == '+'; Op == '-'; Op == '*'; Op == '/' ->
      NumTV = tv_server:fresh_iface(num, C2#ctx.pid),
      ReturnT = if Op == '/' -> {con, float}; true -> NumTV end,
      {
        {lam, LeftT, {lam, RightT, TV}},
        {lam, NumTV, {lam, NumTV, ReturnT}}
      };
    Op == '++' ->
      ListT = {gen, list, tv_server:fresh(C2#ctx.pid)},
      {
        {lam, LeftT, {lam, RightT, TV}},
        {lam, ListT, {lam, ListT, ListT}}
      }
  end,

  {TV, C2#ctx{csts=[Cst | C2#ctx.csts]}};

infer({{Op, _}, Expr}, C) ->
  {ExprT, C1} = infer(Expr, C),
  TV = tv_server:fresh(C1#ctx.pid),

  Cst = if
    Op == '!' -> {{lam, ExprT, TV}, {lam, {con, bool}, {con, bool}}};
    Op == '-' ->
      NumT = tv_server:fresh_iface(num, C1#ctx.pid),
      {{lam, ExprT, TV}, {lam, NumT, NumT}}
  end,

  {TV, C1#ctx{csts=[Cst | C1#ctx.csts]}}.

solve([], #solver{errs=Errs}) when length(Errs) > 0 -> {errors, Errs};
solve([], #solver{subs=Subs}) -> {ok, Subs};
solve(FCs, S) ->
  {Solvable, Unsolved} = lists:partition(fun({_, C}) ->
    length(C#ctx.deps) == 0
  end, FCs),

  if
    length(Solvable) == 0 ->
      % If all function contexts left have dependencies, that means each
      % remaining function either is recursive, is mutually recursive, or
      % depends on a recursive function. We solve all constraints simultaneously
      % to resolve these. Note that any {inst, ...} of these recursive functions
      % won't be generalized because the corresponding type variables are
      % already in the env; we impose this non-polymorphic constraint to infer
      % types with recursion.
      Csts = lists:flatmap(fun({_, C}) -> C#ctx.csts end, Unsolved),
      S1 = unify_csts(resolve_csts(Csts, S), S),
      solve([], S1);

    true ->
      {Solved, S1} = lists:foldl(fun({TV, C}, {Solved, FoldS}) ->
        Csts = resolve_csts(C#ctx.csts, FoldS),
        io:format("solving (~p) ~p~n", [TV, Csts]),
        FoldS1 = unify_csts(Csts, FoldS),
        io:format("subs: ~p~n", [dict:to_list(FoldS1#solver.subs)]),
        {gb_sets:add(TV, Solved), FoldS1}
      end, {gb_sets:new(), S}, Solvable),

      Rest = if
        length(Solvable) == 0 -> [];
        true -> lists:map(fun({TV, C}) ->
          Deps = lists:filter(fun(Dep) ->
            not gb_sets:is_element(Dep, Solved)
          end, C#ctx.deps),
          {TV, C#ctx{deps=Deps}}
        end, Unsolved)
      end,

      solve(Rest, S1)
  end.

resolve_csts([], _) -> [];
resolve_csts([{L, R} | Rest], S) ->
  ResolvedL = resolve(subs(L, S#solver.subs), S),
  ResolvedR = resolve(subs(R, S#solver.subs), S),
  [{ResolvedL, ResolvedR} | resolve_csts(Rest, S)].

resolve({lam, ArgsT, ReturnT}, S) ->
  {lam, resolve(ArgsT, S), resolve(ReturnT, S)};
resolve({tuple, LeftT, RightT}, S) ->
  {tuple, resolve(LeftT, S), resolve(RightT, S)};
resolve({tv, V}, _) -> {tv, V};
resolve({iface, I, V}, _) -> {iface, I, V};
resolve({con, C}, _) -> {con, C};
resolve({gen, C, ParamT}, _) -> {gen, C, ParamT};
resolve({inst, T, EnvList}, S) -> inst(generalize(T, EnvList), S);
resolve(none, _) -> none.

inst({GVs, T}, S) ->
  Subs = gb_sets:fold(fun(V, Subs) ->
    dict:store(V, tv_server:fresh(S#solver.pid), Subs)
  end, dict:new(), GVs),
  subs(T, Subs).

generalize(T, EnvList) ->
  EnvFVs = lists:foldl(fun({_, {_, EnvT}}, S) ->
    gb_sets:union(S, fvs(EnvT))
  end, gb_sets:new(), EnvList),
  GVs = gb_sets:subtract(fvs(T), EnvFVs),
  {GVs, T}.

unify_csts([], S) -> S;
unify_csts([{L, R} | Rest], S) ->
  Subs = S#solver.subs,
  S1 = unify({subs(L, Subs), subs(R, Subs)}, S),
  unify_csts(Rest, S1).

unify({T1, T2}, S) when T1 == T2 -> S;

unify({{lam, ArgsT1, ReturnT1}, {lam, ArgsT2, ReturnT2}}, S) ->
  S1 = unify({ArgsT1, ArgsT2}, S),
  ToUnify = {subs(ReturnT1, S1#solver.subs), subs(ReturnT2, S1#solver.subs)},
  unify(ToUnify, S1);
unify({{tuple, LeftT1, RightT1}, {tuple, LeftT2, RightT2}}, S) ->
  S1 = unify({LeftT1, LeftT2}, S),
  ToUnify = {subs(RightT1, S1#solver.subs), subs(RightT2, S1#solver.subs)},
  unify(ToUnify, S1);

unify({{tv, V}, T}, S) ->
  Occurs = occurs(V, T),
  if Occurs -> S#solver{errs=[{{tv, V}, T} | S#solver.errs]};
     true ->
       S#solver{subs=merge_subs(dict:from_list([{V, T}]), S#solver.subs)}
  end;
unify({T, {tv, V}}, S) -> unify({{tv, V}, T}, S);

unify({{iface, I, V1}, {iface, I, V2}}, S) ->
  Subs = merge_subs(dict:from_list([{V1, {iface, I, V2}}]), S#solver.subs),
  S#solver{subs=Subs};

unify({{iface, I, V}, T}, S) ->
  Instance = instance(T, I),
  if Instance ->
       S#solver{subs=merge_subs(dict:from_list([{V, T}]), S#solver.subs)};
     true -> S#solver{errs=[{{iface, I, V}, T} | S#solver.errs]}
  end;
unify({T, {iface, I, V}}, S) -> unify({{iface, I, V}, T}, S);

unify({{gen, C, ParamT1}, {gen, C, ParamT2}}, S) ->
  unify({ParamT1, ParamT2}, S);

unify({T1, T2}, S) -> S#solver{errs=[{T1, T2} | S#solver.errs]}.

merge_subs(Subs1, Subs2) ->
  dict:merge(fun(K, V1, V2) ->
    error({badarg, K}, [K, V1, V2])
  end, Subs1, Subs2).

instance({con, int}, num) -> true;
instance({con, float}, num) -> true;
instance(_, _) -> false.

subs({lam, ArgsT, ReturnT}, Subs) ->
  {lam, subs(ArgsT, Subs), subs(ReturnT, Subs)};
subs({tuple, LeftT, RightT}, Subs) ->
  {tuple, subs(LeftT, Subs), subs(RightT, Subs)};
subs({tv, V}, Subs) ->
  case dict:find(V, Subs) of
    {ok, TSub} -> subs(TSub, Subs);
    error -> {tv, V}
  end;
subs({iface, I, V}, Subs) ->
  case dict:find(V, Subs) of
    {ok, TSub} -> subs(TSub, Subs);
    error -> {iface, I, V}
  end;
subs({con, C}, _) -> {con, C};
subs({gen, C, ParamT}, Subs) -> {gen, C, subs(ParamT, Subs)};
subs({inst, T, EnvList}, Subs) -> {inst, subs(T, Subs), EnvList};
subs(none, _) -> none.

fvs({lam, ArgsT, ReturnT}) -> gb_sets:union(fvs(ArgsT), fvs(ReturnT));
fvs({tuple, LeftT, RightT}) -> gb_sets:union(fvs(LeftT), fvs(RightT));
fvs({tv, V}) -> gb_sets:from_list([V]);
fvs({iface, _, V}) -> gb_sets:from_list([V]);
fvs({con, _}) -> gb_sets:new();
fvs({gen, _, ParamT}) -> fvs(ParamT);
% fvs({inst, ...}) ommitted; all inst should be resolved
fvs(none) -> gb_sets:new().

occurs(V, {lam, ArgsT, ReturnT}) ->
  occurs(V, ArgsT) or occurs(V, ReturnT);
occurs(V, {tuple, LeftT, RightT}) ->
  occurs(V, LeftT) or occurs(V, RightT);
occurs(V1, {tv, V2}) -> V1 == V2;
occurs(V1, {iface, _, V2}) -> V1 == V2;
occurs(_, {con, _}) -> false;
occurs(V, {gen, _, ParamT}) -> occurs(V, ParamT);
% occurs({inst, ...}) ommitted; all inst should be resolved
occurs(_, none) -> false.
