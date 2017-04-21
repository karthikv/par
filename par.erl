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
% - TODOs in code
% - Type annotations
% - Error messages
% - Basic types: lists, tuples
% - Maybe else types (unit type?)
% - Complex types: ADTs
% - Typeclasses
% - Concurrency
% - Pattern matching
% - Extra type variables for return value of operators like == and +?
% - Better / Efficient EnvList
% - Codegen / Interpreter
% - ETS for fresh variables?

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
    TV = fresh(C#ctx.pid),
    C#ctx{env=dict:store(Name, {fn, TV}, C#ctx.env)}
  end, #ctx{csts=[], env=dict:new(), pid=Pid, deps=[]}, Ast),

  {FCs, C1} = lists:foldl(fun(Node, {FCs, FoldC}) ->
    {TV, FoldC1} = infer(Node, FoldC#ctx{csts=[], deps=[]}),
    {[{TV, FoldC1} | FCs], FoldC1}
  end, {[], C}, Ast),

  case solve(FCs, #solver{subs=dict:new(), errs=[], pid=Pid}) of
    {ok, Subs} ->
      {ok, dict:map(fun(_, {_, T}) -> subs(T, Subs) end, C1#ctx.env)};
    {errors, Errs} -> {errors, Errs}
  end.

infer({fn, Var, Args, Expr}, C) ->
  {ArgsT, C1} = lists:foldr(fun({var, _, ArgName}, {Ts, FoldC}) ->
    TV = fresh(FoldC#ctx.pid),
    {[TV | Ts], FoldC#ctx{
      env=dict:store(ArgName, {arg, TV}, FoldC#ctx.env)
    }}
  end, {[], C}, Args),

  {ReturnT, C2} = infer(Expr, C1),
  T = if length(Args) == 0 -> {lam, none, ReturnT};
         true -> lists:foldr(fun(ArgT, LastT) ->
           {lam, ArgT, LastT}
         end, ReturnT, ArgsT)
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

infer({int, _, _}, C) -> {fresh_iface(num, C#ctx.pid), C};
infer({float, _, _}, C) -> {{con, float}, C};
infer({bool, _, _}, C) -> {{con, bool}, C};
infer({str, _, _}, C) -> {{con, str}, C};

infer({var, _, Name}, C) ->
  % TODO: handle case where can't find variable
  {ok, {Type, T}} = dict:find(Name, C#ctx.env),
  Deps = case Type of
           fn -> [T | C#ctx.deps];
           _ -> C#ctx.deps
         end,
  {{inst, T, dict:to_list(C#ctx.env)}, C#ctx{deps=Deps}};

infer({app, Var, Args}, C) ->
  {ArgsT, C1} = lists:foldr(fun(Arg, {Ts, FoldC}) ->
    {T, FoldC1} = infer(Arg, FoldC),
    {[T | Ts], FoldC1}
  end, {[], C}, Args),

  {VarT, C2} = infer(Var, C1),
  TV = fresh(C2#ctx.pid),
  T = lists:foldr(fun(ArgT, LastT) -> {lam, ArgT, LastT} end, TV, ArgsT),
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

  TV = fresh(C#ctx.pid),
  {TV, C3#ctx{
    csts=[{{con, bool}, ExprT}, {TV, ThenT}, {TV, ElseT} | C3#ctx.csts]}
  };

infer({{Op, _}, Left, Right}, C) ->
  {LeftT, C1} = infer(Left, C),
  {RightT, C2} = infer(Right, C1),

  TV = fresh(C2#ctx.pid),

  Cst = if
    Op == '=='; Op == '!=' ->
      OperandTV = fresh(C2#ctx.pid),
      {
        {lam, LeftT, {lam, RightT, TV}},
        {lam, OperandTV, {lam, OperandTV, {con, bool}}}
      };
    Op == '||'; Op == '&&' -> {
      {lam, LeftT, {lam, RightT, TV}},
      {lam, {con, bool}, {lam, {con, bool}, {con, bool}}}
    };
    Op == '>'; Op == '<'; Op == '>='; Op == '<=' ->
      NumT = fresh_iface(num, C2#ctx.pid),
      {
        {lam, LeftT, {lam, RightT, TV}},
        {lam, NumT, {lam, NumT, {con, bool}}}
      };
    Op == '+'; Op == '-'; Op == '*'; Op == '/' ->
      NumT = fresh_iface(num, C2#ctx.pid),
      ReturnT = if Op == '/' -> {con, float}; true -> NumT end,
      {
        {lam, LeftT, {lam, RightT, TV}},
        {lam, NumT, {lam, NumT, ReturnT}}
      };
    Op == '++' -> {
      {lam, LeftT, {lam, RightT, TV}},
      {lam, {con, str}, {lam, {con, str}, {con, str}}}
    }
  end,

  {TV, C2#ctx{csts=[Cst | C2#ctx.csts]}};

infer({{Op, _}, Expr}, C) ->
  {ExprT, C1} = infer(Expr, C),
  TV = fresh(C1#ctx.pid),

  Cst = if
    Op == '!' -> {{lam, ExprT, TV}, {lam, {con, bool}, {con, bool}}};
    Op == '-' ->
      NumT = fresh_iface(num, C1#ctx.pid),
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
        io:format("solving before subs (~p) ~p~n", [TV, C#ctx.csts]),
        io:format("solving after subs (~p) ~p~n", [TV, Csts]),
        io:format("result: ~p~n", [unify_csts(Csts, FoldS)]),
        {gb_sets:add(TV, Solved), unify_csts(Csts, FoldS)}
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
resolve({tv, TV}, _) -> {tv, TV};
resolve({iface, I, TV}, _) -> {iface, I, TV};
resolve({con, T}, _) -> {con, T};
resolve({inst, T, EnvList}, S) -> inst(generalize(T, EnvList), S);
resolve(none, _) -> none.

inst({GTVs, T}, S) ->
  Subs = gb_sets:fold(fun(GTV, Subs) ->
    dict:store(GTV, fresh(S#solver.pid), Subs)
  end, dict:new(), GTVs),
  subs(T, Subs).

generalize(T, EnvList) ->
  EnvFTVs = lists:foldl(fun({_, {_, EnvT}}, S) ->
    gb_sets:union(S, ftvs(EnvT))
  end, gb_sets:new(), EnvList),
  GTVs = gb_sets:subtract(ftvs(T), EnvFTVs),
  {GTVs, T}.

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

unify({{tv, TV}, T}, S) ->
  Occurs = occurs(TV, T),
  if Occurs -> S#solver{errs=[{{tv, TV}, T} | S#solver.errs]};
     true ->
       S#solver{subs=merge_subs(dict:from_list([{TV, T}]), S#solver.subs)}
  end;
unify({T, {tv, TV}}, S) -> unify({{tv, TV}, T}, S);

unify({{iface, I, TV1}, {iface, I, TV2}}, S) ->
  Subs = merge_subs(dict:from_list([{TV1, {iface, I, TV2}}]), S#solver.subs),
  S#solver{subs=Subs};

unify({{iface, I, TV}, T}, S) ->
  Instance = instance(T, I),
  if Instance ->
       S#solver{subs=merge_subs(dict:from_list([{TV, T}]), S#solver.subs)};
     true -> S#solver{errs=[{{iface, I, TV}, T} | S#solver.errs]}
  end;
unify({T, {iface, I, TV}}, S) -> unify({{iface, I, TV}, T}, S);

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
subs({tv, TV}, Subs) ->
  case dict:find(TV, Subs) of
    {ok, TSub} -> subs(TSub, Subs);
    error -> {tv, TV}
  end;
subs({iface, I, TV}, Subs) ->
  case dict:find(TV, Subs) of
    {ok, TSub} -> subs(TSub, Subs);
    error -> {iface, I, TV}
  end;
subs({con, T}, _) -> {con, T};
subs({inst, T, EnvList}, Subs) -> {inst, subs(T, Subs), EnvList};
subs(none, _) -> none.

ftvs({lam, ArgsT, ReturnT}) -> gb_sets:union(ftvs(ArgsT), ftvs(ReturnT));
ftvs({tv, TV}) -> gb_sets:from_list([TV]);
ftvs({iface, _, TV}) -> gb_sets:from_list([TV]);
ftvs({con, _}) -> gb_sets:new();
% ftvs({inst, ...}) ommitted; all inst should be resolved
ftvs(none) -> gb_sets:new().

occurs(TV, {lam, ArgsT, ReturnT}) ->
  occurs(TV, ArgsT) or occurs(TV, ReturnT);
occurs(TV1, {tv, TV2}) -> TV1 == TV2;
occurs(TV1, {iface, _, TV2}) -> TV1 == TV2;
% occurs({inst, ...}) ommitted; all inst should be resolved
occurs(_, {con, _}) -> false;
occurs(_, none) -> false.

fresh(Pid) -> {tv, tv_server:fresh(Pid)}.
fresh_iface(I, Pid) -> {iface, I, tv_server:fresh(Pid)}.
