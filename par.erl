-module(par).
-export([reload/1, infer_prg/1, subs/2, fvs/1]).

-record(ctx, {csts, env, pid, deps}).
-record(solver, {subs, errs, pid}).

-ifdef(release).
  -define(LOG(Prefix, Value), true).
-else.
  -define(
    LOG(Prefix, Value),
    io:format("~n(~p:~p) ~s:~n~p~n", [?MODULE, ?LINE, Prefix, Value])
  ).
-endif.

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
%   env - maps variable name to Scheme
%   count - a monotonically increasing count used to generate fresh TVs
%
% TODO:
% - TODOs in code (non-unification error cases)
% - Error messages
% - Global variables
% - Interfaces in type signature, maybe A ~ Num?
% - Complex types: ADTs
% - Imports
% - Typeclasses + generics w/o concrete types
% - Concurrency
% - Pattern matching
% - Exceptions
% - Code generation
% - Update naming conventions
%
% - + instead of ++ and - instead of --?
% - Reverse csts before solving for better error messages?
% - Make true/false capitalized?
% - Syntax for lambda with no arg?
% - Maybe else w/ unit type?
% - Operation: nth element of tuple?
% - Unit as valid expression?

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
  tv_server:reload(),

  code:purge(?MODULE),
  {ok, _} = compile:file(?MODULE),
  code:load_file(?MODULE).

infer_prg(Prg) ->
  {ok, Tokens, _} = lexer:string(Prg),
  {ok, Ast} = parser:parse(Tokens),
  ?LOG("AST", Ast),
  {ok, Pid} = tv_server:start_link(),

  C = lists:foldl(fun(Node, C) ->
    case Node of
      {fn, {var, _, Name}, _, _} ->
        % TODO: what if name already exists?
        TV = tv_server:fresh(C#ctx.pid),
        add_env(Name, {fn, TV}, C);
      _ -> C
    end
  end, #ctx{csts=[], env=#{}, pid=Pid, deps=[]}, Ast),

  {_, _, FCs, C1} = lists:foldl(fun(Node, {ExpName, SigT, FCs, FoldC}) ->
    if
      % TODO: handle error
      ExpName =/= none -> {fn, {var, _, ExpName}, _, _} = Node;
      true -> none
    end,

    case Node of
      {fn, _, _, _} ->
        {TV, FoldC1} = infer(Node, FoldC#ctx{csts=[], deps=[]}),
        Csts = if
          SigT == none -> FoldC1#ctx.csts;
          true -> [{TV, SigT} | FoldC1#ctx.csts]
        end,
        FoldC2 = FoldC1#ctx{csts=Csts},
        {none, none, [{TV, FoldC2} | FCs], FoldC2};
      {sig, {var, _, Name}, _} ->
        {T, FoldC1} = infer(Node, FoldC#ctx{csts=[], deps=[]}),
        {Name, T, FCs, FoldC1}
    end
  end, {none, none, [], C}, Ast),

  Result = case solve(FCs, #solver{subs=#{}, errs=[], pid=Pid}) of
    {ok, Subs} ->
      {ok, maps:map(fun(_, {_, T}) -> subs(T, Subs) end, C1#ctx.env), Ast};
    {errors, Errs} -> {errors, Errs}
  end,

  ok = tv_server:stop(Pid),
  Result.

infer({fn, Var, Args, Expr}, C) ->
  {ArgsTRev, C1} = lists:foldl(fun({var, _, ArgName}, {Ts, FoldC}) ->
    TV = tv_server:fresh(FoldC#ctx.pid),
    {[TV | Ts], add_env(ArgName, {arg, TV}, FoldC)}
  end, {[], C}, Args),

  {ReturnT, C2} = infer(Expr, C1),
  T = if
    length(Args) == 0 -> {lam, none, ReturnT};
    true -> lists:foldl(fun(ArgT, LastT) ->
      {lam, ArgT, LastT}
    end, ReturnT, ArgsTRev)
  end,

  case Var of
    {var, _, Name} ->
      #{Name := {_, FnTV}} = C#ctx.env,
      {FnTV, C2#ctx{
        csts=[{FnTV, T} | C2#ctx.csts],
        % restore original env
        env=C#ctx.env
      }};
    none ->
      % restore original env
      {T, C2#ctx{env=C#ctx.env}}
  end;

infer({sig, _, Sig}, C) ->
  {SigT, C1} = infer(Sig, C),
  {norm_sig_type(SigT, C#ctx.pid), C1};

infer({expr_sig, Expr, Sig}, C) ->
  {ExprT, C1} = infer(Expr, C),
  {SigT, C2} = infer(Sig, C1),

  NormSigT = norm_sig_type(SigT, C#ctx.pid),
  {ExprT, add_csts({ExprT, NormSigT}, C2)};

infer({sig_lam, SigArgsT, SigReturnT}, C) ->
  {ArgsT, C1} = infer(SigArgsT, C),
  {ReturnT, C2} = infer(SigReturnT, C1),
  {{lam, ArgsT, ReturnT}, C2};
infer({sig_tuple, SigLeftT, SigRightT}, C) ->
  {LeftT, C1} = infer(SigLeftT, C),
  {RightT, C2} = infer(SigRightT, C1),
  {{tuple, LeftT, RightT}, C2};
infer({sig_iface, SigTV, SigCon}, C) ->
  {{tv, V, none, GVs}, C1} = infer(SigTV, C),
  {{con, I}, C2} = infer(SigCon, C1),
  {{tv, V, I, GVs}, C2};
infer({sig_gen, SigCon, SigParamT}, C) ->
  {{con, T}, C1} = infer(SigCon, C),
  {ParamT, C2} = infer(SigParamT, C1),
  {{gen, T, ParamT}, C2};
infer({sig_tv, _, V}, C) -> {{tv, V, none, gb_sets:new()}, C};
% TODO: ensure these types are valid
infer({sig_con, _, Con}, C) -> {{con, list_to_atom(Con)}, C};
infer(none, C) -> {none, C};

infer({int, _, _}, C) -> {tv_server:fresh('Num', C#ctx.pid), C};
infer({float, _, _}, C) -> {{con, 'Float'}, C};
infer({bool, _, _}, C) -> {{con, 'Bool'}, C};
infer({str, _, _}, C) -> {{con, 'String'}, C};
infer({atom, _, _}, C) -> {{con, 'Atom'}, C};

infer({list, Elems}, C) ->
  TV = tv_server:fresh(C#ctx.pid),
  {Csts, C1} = lists:foldl(fun(Elem, {FoldCsts, FoldC}) ->
    {ElemT, FoldC1} = infer(Elem, FoldC),
    {[{ElemT, TV} | FoldCsts], FoldC1}
  end, {[], C}, Elems),

  {{gen, 'List', TV}, add_csts(Csts, C1)};

infer({tuple, Elems}, C) ->
  {ElemsTRev, C1} = lists:foldl(fun(Elem, {FoldElemsT, FoldC}) ->
    {ElemT, FoldC1} = infer(Elem, FoldC),
    {[ElemT | FoldElemsT], FoldC1}
  end, {[], C}, Elems),

  T = lists:foldl(fun(ElemT, LastT) ->
    {tuple, ElemT, LastT}
  end, hd(ElemsTRev), tl(ElemsTRev)),
  {T, C1};

infer({map, Pairs}, C) ->
  KeyTV = tv_server:fresh(C#ctx.pid),
  ValueTV = tv_server:fresh(C#ctx.pid),

  {Csts, C1} = lists:foldl(fun({Key, Value}, {FoldCsts, FoldC}) ->
    {KeyT, FoldC1} = infer(Key, FoldC),
    {ValueT, FoldC2} = infer(Value, FoldC1),
    {[{KeyT, KeyTV}, {ValueT, ValueTV} | FoldCsts], FoldC2}
  end, {[], C}, Pairs),

  {{gen, 'Map', {tuple, KeyTV, ValueTV}}, add_csts(Csts, C1)};

infer({var, _, Name}, C) ->
  % TODO: handle case where can't find variable
  {ok, {Type, T}} = maps:find(Name, C#ctx.env),
  Deps = case Type of
           fn -> [T | C#ctx.deps];
           _ -> C#ctx.deps
         end,
  {{inst, T, maps:to_list(C#ctx.env)}, C#ctx{deps=Deps}};

infer({app, Expr, Args}, C) ->
  {ArgsTRev, C1} = lists:foldl(fun(Arg, {Ts, FoldC}) ->
    {T, FoldC1} = infer(Arg, FoldC),
    {[T | Ts], FoldC1}
  end, {[], C}, Args),

  {ExprT, C2} = infer(Expr, C1),
  TV = tv_server:fresh(C2#ctx.pid),
  T = if
    length(ArgsTRev) == 0 -> {lam, none, TV};
    true ->
      lists:foldl(fun(ArgT, LastT) ->
        {lam, ArgT, LastT}
      end, TV, ArgsTRev)
  end,

  {TV, add_csts({T, ExprT}, C2)};

infer({native, {atom, _, Module}, {var, _, Name}, Arity}, C) ->
  % TODO: handle case where this fails
  true = erlang:function_exported(Module, list_to_atom(Name), Arity),
  T = if
    Arity == 0 -> {lam, none, tv_server:fresh(C#ctx.pid)};
    true ->
      lists:foldl(fun(_, LastT) ->
        {lam, tv_server:fresh(C#ctx.pid), LastT}
      end, tv_server:fresh(C#ctx.pid), lists:seq(1, Arity))
  end,

  {T, C};

infer({{'let', _}, Inits, Expr}, C) ->
  C1 = lists:foldl(fun({{var, _, Name}, InitExpr}, FoldC) ->
    {T, FoldC1} = infer(InitExpr, FoldC),
    add_env(Name, {'let', T}, FoldC1)
  end, C, Inits),

  {T, C2} = infer(Expr, C1),
  {T, C2#ctx{env=C#ctx.env}};

infer({{'if', _}, Expr, Then, Else}, C) ->
  {ExprT, C1} = infer(Expr, C),
  {ThenT, C2} = infer(Then, C1),
  {ElseT, C3} = infer(Else, C2),

  TV = tv_server:fresh(C#ctx.pid),
  {TV, add_csts([{{con, 'Bool'}, ExprT}, {TV, ThenT}, {TV, ElseT}], C3)};

infer({{Op, _}, Left, Right}, C) ->
  {LeftT, C1} = infer(Left, C),
  {RightT, C2} = infer(Right, C1),

  TV = tv_server:fresh(C2#ctx.pid),

  Cst = if
    Op == '=='; Op == '!=' ->
      OperandTV = tv_server:fresh(C2#ctx.pid),
      {
        {lam, LeftT, {lam, RightT, TV}},
        {lam, OperandTV, {lam, OperandTV, {con, 'Bool'}}}
      };
    Op == '||'; Op == '&&' -> {
      {lam, LeftT, {lam, RightT, TV}},
      {lam, {con, 'Bool'}, {lam, {con, 'Bool'}, {con, 'Bool'}}}
    };
    Op == '>'; Op == '<'; Op == '>='; Op == '<=' ->
      NumTV = tv_server:fresh('Num', C2#ctx.pid),
      {
        {lam, LeftT, {lam, RightT, TV}},
        {lam, NumTV, {lam, NumTV, {con, 'Bool'}}}
      };
    Op == '+'; Op == '-'; Op == '*'; Op == '/' ->
      NumTV = tv_server:fresh('Num', C2#ctx.pid),
      ReturnT = if Op == '/' -> {con, 'Float'}; true -> NumTV end,
      {
        {lam, LeftT, {lam, RightT, TV}},
        {lam, NumTV, {lam, NumTV, ReturnT}}
      };
    Op == '++' ->
      OperandTV = tv_server:fresh('Concatable', C2#ctx.pid),
      {
        {lam, LeftT, {lam, RightT, TV}},
        {lam, OperandTV, {lam, OperandTV, OperandTV}}
      };
    Op == '--' ->
      OperandTV = tv_server:fresh('Separable', C2#ctx.pid),
      {
        {lam, LeftT, {lam, RightT, TV}},
        {lam, OperandTV, {lam, OperandTV, OperandTV}}
      }
  end,

  {TV, add_csts(Cst, C2)};

infer({{Op, _}, Expr}, C) ->
  {ExprT, C1} = infer(Expr, C),
  TV = tv_server:fresh(C1#ctx.pid),

  Cst = if
    Op == '!' -> {{lam, ExprT, TV}, {lam, {con, 'Bool'}, {con, 'Bool'}}};
    Op == '#' ->
      ElemT = tv_server:fresh(C1#ctx.pid),
      {{lam, ExprT, TV}, {lam, {gen, 'List', ElemT}, {gen, 'Set', ElemT}}};
    Op == '-' ->
      NumT = tv_server:fresh('Num', C1#ctx.pid),
      {{lam, ExprT, TV}, {lam, NumT, NumT}}
  end,

  {TV, add_csts(Cst, C1)}.

add_env(Name, Value, C) ->
  C#ctx{env=(C#ctx.env)#{Name => Value}}.

add_csts(Csts, C) ->
  case is_list(Csts) of
    true -> C#ctx{csts=Csts ++ C#ctx.csts};
    false -> C#ctx{csts=[Csts | C#ctx.csts]}
  end.

norm_sig_type(SigT, Pid) ->
  % TODO: is it more intuitive to change each fv to *fv and then replace?
  FVList = gb_sets:to_list(fvs(SigT)),
  NewFVList = lists:map(fun(_) -> tv_server:next_name(Pid) end, FVList),
  FVSubs = maps:from_list(lists:zip(FVList, NewFVList)),

  GVs = gb_sets:from_list(NewFVList),
  GVSubs = maps:from_list(lists:map(fun(FV) ->
    {FV, {add_gvs, GVs}}
  end, NewFVList)),

  subs(subs(SigT, FVSubs), GVSubs).

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
        FoldS1 = unify_csts(Csts, FoldS),
        ?LOG("Csts", Csts),
        ?LOG("Subs", maps:to_list(FoldS1#solver.subs)),
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
resolve({tv, V, I, GVs}, _) -> {tv, V, I, GVs};
resolve({con, Con}, _) -> {con, Con};
resolve({gen, Con, ParamT}, _) -> {gen, Con, ParamT};
resolve({inst, T, EnvList}, S) -> inst(generalize(T, EnvList), S);
resolve(none, _) -> none.

inst({GVs, T}, S) ->
  Subs = gb_sets:fold(fun(V, Subs) ->
    Subs#{V => tv_server:next_name(S#solver.pid)}
  end, #{}, GVs),
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

unify({{tv, V, I1, GVs1}, {tv, V, I2, GVs2}}, _) ->
  error({badarg, V, I1, GVs1, I2, GVs2});
unify({{tv, V1, I1, GVs1}, {tv, V2, I2, GVs2}}, S) ->
  Err = {{tv, V1, I1, GVs1}, {tv, V2, I2, GVs2}},
  Occurs = gb_sets:is_member(V1, GVs2) or gb_sets:is_member(V2, GVs1),
  AllV1 = gb_sets:is_member(V1, GVs1),
  AllV2 = gb_sets:is_member(V2, GVs2),

  if
    Occurs -> add_err(Err, S);

    % V1 is the most (or equally) constraining; change V2 -> V1
    I1 == I2, AllV1 ->
      add_sub(V2, {tv, V1, I1, gb_sets:union(GVs1, GVs2)}, S);

    % V2 is the most (or equally) constraining; change V1 -> V2
    I1 == I2, not AllV1 ->
      add_sub(V1, {tv, V2, I2, gb_sets:union(GVs2, GVs1)}, S);

    % can substitute V2 for anything; change V2 -> V1
    I2 == none, not AllV2 ->
      add_sub(V2, {tv, V1, I1, gb_sets:union(GVs1, GVs2)}, S);

    % can substitute V1 for anything; change V1 -> V2
    I1 == none, not AllV1 ->
      add_sub(V1, {tv, V2, I2, gb_sets:union(GVs2, GVs1)}, S);

    % We're now guaranteed three things:
    % (1) I1 =/= I2
    % (2) I2 =/= none or AllV2
    % (3) I1 =/= none or AllV1
    %
    % (1) means the interfaces differ, (2) means we can't change V2 -> V1,
    % and (3) means we can't change V1 -> V2. We're out of options.
    true -> add_err(Err, S)
  end;
unify({{tv, V, I, GVs}, T}, S) ->
  Err = {{tv, V, I, GVs}, T},
  Occurs = occurs(gb_sets:add(V, GVs), T),
  Instance = not gb_sets:is_member(V, GVs) and ((I == none) or instance(T, I)),

  if
    Occurs -> add_err(Err, S);
    Instance -> add_sub(V, T, S);
    true -> add_err(Err, S)
  end;
unify({T, {tv, V, I, GVs}}, S) -> unify({{tv, V, I, GVs}, T}, S);

unify({{gen, C, ParamT1}, {gen, C, ParamT2}}, S) ->
  unify({ParamT1, ParamT2}, S);

unify({T1, T2}, S) -> S#solver{errs=[{T1, T2} | S#solver.errs]}.

add_sub(Key, Value, S) ->
  case maps:find(Key, S#solver.subs) of
    {ok, Existing} -> error({badarg, Key, Existing, Value});
    error -> S#solver{subs=(S#solver.subs)#{Key => Value}}
  end.

add_err(Err, S) ->
  S#solver{errs=[Err | S#solver.errs]}.

instance({con, 'Int'}, 'Num') -> true;
instance({con, 'Float'}, 'Num') -> true;
instance({con, 'String'}, 'Concatable') -> true;
instance({gen, 'List', _}, 'Concatable') -> true;
instance({gen, 'Map', _}, 'Concatable') -> true;
instance({gen, 'Set', _}, 'Concatable') -> true;
instance({gen, 'List', _}, 'Separable') -> true;
instance({gen, 'Set', _}, 'Separable') -> true;
instance(_, _) -> false.

subs({lam, ArgsT, ReturnT}, Subs) ->
  {lam, subs(ArgsT, Subs), subs(ReturnT, Subs)};
subs({tuple, LeftT, RightT}, Subs) ->
  {tuple, subs(LeftT, Subs), subs(RightT, Subs)};
subs({tv, V, I, GVs}, Subs) ->
  case maps:find(V, Subs) of
    {ok, {add_gvs, NewGVs}} -> {tv, V, I, gb_sets:union(GVs, NewGVs)};
    {ok, Value} ->
      Sub = if
        % Replacing with a new type entirely
        is_tuple(Value) -> Value;
        % Changing name due to instantiation; GVs don't carry over.
        true -> {tv, Value, I, gb_sets:new()}
      end,
      subs(Sub, Subs);
    error -> {tv, V, I, GVs}
  end;
subs({con, Con}, _) -> {con, Con};
subs({gen, Con, ParamT}, Subs) -> {gen, Con, subs(ParamT, Subs)};
subs({inst, T, EnvList}, Subs) -> {inst, subs(T, Subs), EnvList};
subs(none, _) -> none.

fvs({lam, ArgsT, ReturnT}) -> gb_sets:union(fvs(ArgsT), fvs(ReturnT));
fvs({tuple, LeftT, RightT}) -> gb_sets:union(fvs(LeftT), fvs(RightT));
fvs({tv, V, _, _}) -> gb_sets:from_list([V]);
fvs({con, _}) -> gb_sets:new();
fvs({gen, _, ParamT}) -> fvs(ParamT);
% fvs({inst, ...}) ommitted; all inst should be resolved
fvs(none) -> gb_sets:new().

occurs(S, {lam, ArgsT, ReturnT}) ->
  occurs(S, ArgsT) or occurs(S, ReturnT);
occurs(S, {tuple, LeftT, RightT}) ->
  occurs(S, LeftT) or occurs(S, RightT);
occurs(S, {tv, V, _, GVs}) -> not gb_sets:is_disjoint(S, gb_sets:add(V, GVs));
occurs(_, {con, _}) -> false;
occurs(S, {gen, _, ParamT}) -> occurs(S, ParamT);
% occurs({inst, ...}) ommitted; all inst should be resolved
occurs(_, none) -> false.
