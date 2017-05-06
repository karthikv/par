-module(par).
-export([reload/1, infer_prg/1, subs/2, fvs/1, pretty/1]).

-record(ctx, {gnr, gnrs, env, pid}).
-record(solver, {subs, errs, schemes, rigid_vs, pid}).

-record(gnr, {v, env, csts, deps, index, low_link, on_stack}).
-record(tarjan, {stack, map, next_index, solver}).

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
% - Mod operator
% - Complex types: ADTs
% - Imports
% - Typeclasses + generics w/o concrete types (HKTs)
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
% - Operation: nth element of tuple?
% - Unit as valid expression?
% - Force all block expressions except last to be type ()?

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
  %% ?LOG("AST", Ast),
  {ok, Pid} = tv_server:start_link(),

  C = lists:foldl(fun(Node, FoldC) ->
    case Node of
      {global, {var, _, Name}, _} ->
        % TODO: what if name already exists?
        TV = tv_server:fresh(FoldC#ctx.pid),
        add_env(Name, {add_dep, TV}, FoldC);

      % TODO: register valid type for each enum/struct

      _ -> FoldC
    end
  end, #ctx{gnrs=[], env=#{}, pid=Pid}, Ast),

  C1 = lists:foldl(fun(Node, FoldC) ->
    case Node of
      {enum, _, _} ->
        {_, FoldC1} = infer(Node, FoldC),
        FoldC1;
      _ -> FoldC
    end
  end, C, Ast),

  {_, _, C2} = lists:foldl(fun(Node, {ExpName, SigT, FoldC}) ->
    if
      % TODO: handle error
      ExpName /= none -> {global, {var, _, ExpName}, _} = Node;
      true -> none
    end,

    case Node of
      {global, {var, _, Name}, Expr} ->
        #{Name := {add_dep, TV}} = FoldC#ctx.env,
        % for generalization, use env that doesn't contain any globals
        % TODO: should anything be in this map?
        FoldC1 = new_gnr(TV, FoldC),
        {T, FoldC2} = infer(Expr, FoldC1),

        Csts = if
          SigT == none -> [{TV, T}];
          true -> [{TV, T}, {TV, SigT}]
        end,
        FoldC3 = add_csts(Csts, FoldC2),

        {none, none, finish_gnr(FoldC3, FoldC#ctx.gnr)};

      {sig, {var, _, Name}, _} ->
        {T, FoldC1} = infer(Node, FoldC),
        {Name, T, FoldC1};

      % we've already processed enums/structs
      _ -> {ExpName, SigT, FoldC}
    end
  end, {none, none, C1}, Ast),

  S = #solver{subs=#{}, errs=[], schemes=#{}, pid=Pid},
  Result = case solve(C2#ctx.gnrs, S) of
    {ok, Subs} ->
      {ok, maps:map(fun(_, {_, T}) -> subs(T, Subs) end, C2#ctx.env), Ast};
    {errors, Errs} -> {errors, Errs}
  end,

  ok = tv_server:stop(Pid),
  Result.

infer({fn, Args, Expr}, C) ->
  {ArgsTRev, C1} = lists:foldl(fun({var, _, ArgName}, {Ts, FoldC}) ->
    ArgTV = tv_server:fresh(FoldC#ctx.pid),
    {[ArgTV | Ts], add_env(ArgName, {no_dep, ArgTV}, FoldC)}
  end, {[], C}, Args),

  {ReturnT, C2} = infer(Expr, C1),
  T = if
    length(Args) == 0 -> {lam, none, ReturnT};
    true -> lists:foldl(fun(ArgT, LastT) ->
      {lam, ArgT, LastT}
    end, ReturnT, ArgsTRev)
  end,

  % restore original env
  {T, C2#ctx{env=C#ctx.env}};

infer({sig, _, Sig}, C) ->
  {SigT, C1} = infer(Sig, C),
  {norm_sig_type(SigT, C#ctx.pid), C1};

infer({expr_sig, Expr, Sig}, C) ->
  G = C#ctx.gnr,
  TV = tv_server:fresh(C#ctx.pid),

  {ExprT, C1} = infer(Expr, new_gnr(TV, C)),
  {SigT, C2} = infer(Sig, C1),
  NormSigT = norm_sig_type(SigT, C2#ctx.pid),

  C3 = add_csts([{TV, ExprT}, {TV, NormSigT}], C2),
  {tv, V, _, _} = TV,
  {{inst, TV}, finish_gnr(C3, G#gnr{deps=[V | G#gnr.deps]})};

infer({lam_expr, Arg, Return}, C) ->
  {ArgT, C1} = infer(Arg, C),
  {ReturnT, C2} = infer(Return, C1),
  {{lam, ArgT, ReturnT}, C2};
infer({tuple_expr, Left, Right}, C) ->
  {LeftT, C1} = infer(Left, C),
  {RightT, C2} = infer(Right, C1),
  {{tuple, LeftT, RightT}, C2};
infer({iface_expr, TVToken, ConToken}, C) ->
  {{tv, V, none, All}, C1} = infer(TVToken, C),
  {{con, I}, C2} = infer(ConToken, C1),
  {{tv, V, I, All}, C2};
infer({gen_expr, ConToken, Param}, C) ->
  {{con, T}, C1} = infer(ConToken, C),
  {ParamT, C2} = infer(Param, C1),
  {{gen, T, ParamT}, C2};
infer({tv_token, _, Name}, C) -> {{tv, Name, none, true}, C};
% TODO: ensure these types are valid except when creating a new type
infer({con_token, _, Name}, C) -> {{con, list_to_atom(Name)}, C};

%% infer({enum, ConToken, Options}, C) ->
%%   {T, C1} = infer(ConToken, C),
%%   C2 = lists:foldl(fun({option, {con_token, _, Name}, Args}, FoldC) ->
%%     {ArgsTRev, FoldC1} = lists:foldl(fun(Arg, {Ts, InnerC}) ->
%%       {ArgT, InnerC1} = infer(Arg, InnerC),
%%       {[ArgT | Ts], InnerC1}
%%     end, {[], FoldC}, Args),
%%
%%     OptionT = lists:foldl(fun(ArgT, LastT) ->
%%       {lam, ArgT, LastT}
%%     end, T, ArgsTRev),
%%     NormOptionT = norm_sig_type(OptionT, C#ctx.pid),
%%
%%     % TODO: what if name already exists?
%%     TV = tv_server:fresh(C#ctx.pid),
%%     add_env(Name, {enum, TV}, add_csts({TV, NormOptionT}, FoldC1))
%%   end, C1, Options),
%%
%%   {T, C2};

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
  case maps:find(Name, C#ctx.env) of
    {ok, {add_dep, EnvTV}} ->
      {tv, V, _, _} = EnvTV,
      G = C#ctx.gnr,
      G1 = G#gnr{deps=[V | G#gnr.deps]},

      % We need to defer instantiation until we start solving constraints.
      % Otherwise, we don't know the real types of these variables, and can't
      % instantiate properly.
      {{inst, EnvTV}, C#ctx{gnr=G1}};

    {ok, {_, EnvTV}} ->
      {EnvTV, C}
  end;

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

infer({{'if', _}, Expr, Then, Else}, C) ->
  {ExprT, C1} = infer(Expr, C),
  {ThenT, C2} = infer(Then, C1),

  case Else of
    none -> {none, add_csts([{{con, 'Bool'}, ExprT}], C2)};
    _ ->
      {ElseT, C3} = infer(Else, C2),
      TV = tv_server:fresh(C#ctx.pid),
      {TV, add_csts([{{con, 'Bool'}, ExprT}, {TV, ThenT}, {TV, ElseT}], C3)}
  end;

infer({{'let', _}, Inits, Expr}, C) ->
  C1 = lists:foldl(fun({{var, _, Name}, _}, FoldC) ->
    TV = tv_server:fresh(FoldC#ctx.pid),
    % TODO: name conflicts?
    add_env(Name, {add_dep, TV}, FoldC)
  end, C, Inits),

  C2 = lists:foldl(fun({{var, _, Name}, InitExpr}, FoldC) ->
    #{Name := {add_dep, TV}} = FoldC#ctx.env,
    % for generalization, use env that doesn't contain let variables
    {T, FoldC1} = infer(InitExpr, new_gnr(TV, FoldC)),
    FoldC2 = add_csts({TV, T}, FoldC1),
    finish_gnr(FoldC2, FoldC#ctx.gnr)
  end, C1, Inits),

  {T, C3} = infer(Expr, C2),
  {T, C3#ctx{env=C#ctx.env}};

infer({block, Exprs}, C) ->
  lists:foldl(fun(Expr, {_, FoldC}) ->
    infer(Expr, FoldC)
  end, {none, C}, Exprs);

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
      {{lam, ExprT, TV}, {lam, NumT, NumT}};
    Op == 'discard' -> {TV, none}
  end,

  {TV, add_csts(Cst, C1)}.

add_env(Name, Value, C) ->
  {_, {tv, _, _, _}} = Value,
  C#ctx{env=(C#ctx.env)#{Name => Value}}.

new_gnr({tv, V, _, _}, C) ->
  G = #gnr{v=V, env=C#ctx.env, csts=[], deps=[]},
  C#ctx{gnr=G}.

finish_gnr(C, NewG) ->
  C#ctx{gnrs=[C#ctx.gnr | C#ctx.gnrs], gnr=NewG}.

add_csts(Csts, C) ->
  G = C#ctx.gnr,
  G1 = case is_list(Csts) of
    true -> G#gnr{csts=Csts ++ G#gnr.csts};
    false -> G#gnr{csts=[Csts | G#gnr.csts]}
  end,

  C#ctx{gnr=G1}.

norm_sig_type(SigT, Pid) ->
  % TODO: is it more intuitive to change each fv to *fv and then replace?
  FVList = gb_sets:to_list(fvs(SigT)),
  NewFVList = lists:map(fun(_) ->
    {all, tv_server:next_name(Pid)}
  end, FVList),
  FVSubs = maps:from_list(lists:zip(FVList, NewFVList)),
  subs(SigT, FVSubs).

solve(Gs, S) ->
  Map = lists:foldl(fun(G, FoldMap) -> FoldMap#{G#gnr.v => G} end, #{}, Gs),
  ?LOG("Gs", lists:map(fun(G) -> G#gnr{csts=pretty_csts(G#gnr.csts)} end, Gs)),

  T = lists:foldl(fun(#gnr{v=V}, FoldT) ->
    #{V := #gnr{index=Index}} = FoldT#tarjan.map,
    if
      Index == undefined -> connect(V, FoldT#tarjan{stack=[]});
      true -> FoldT
    end
  end, #tarjan{map=Map, next_index=0, solver=S}, Gs),

  case T#tarjan.solver of
    #solver{errs=Errs} when length(Errs) > 0 -> {errors, Errs};
    #solver{subs=Subs} -> {ok, Subs}
  end.

connect(V, #tarjan{stack=Stack, map=Map, next_index=NextIndex, solver=S}) ->
  #{V := G} = Map,
  Stack1 = [V | Stack],
  Map1 = Map#{V := G#gnr{index=NextIndex, low_link=NextIndex, on_stack=true}},

  T1 = #tarjan{stack=Stack1, map=Map1, next_index=NextIndex + 1, solver=S},
  T2 = lists:foldl(fun(AdjV, FoldT) ->
    #{AdjV := #gnr{index=AdjIndex, on_stack=AdjOnStack}} = FoldT#tarjan.map,

    if
      AdjIndex == undefined ->
        FoldT1 = connect(AdjV, FoldT),
        FoldMap1 = FoldT1#tarjan.map,
        #{V := FoldG1, AdjV := AdjG1} = FoldMap1,
        FoldG2 = FoldG1#gnr{
          low_link=min(FoldG1#gnr.low_link, AdjG1#gnr.low_link)
        },
        FoldT1#tarjan{map=FoldMap1#{V := FoldG2}};

      AdjOnStack ->
        FoldMap = FoldT#tarjan.map,
        #{V := FoldG} = FoldMap,
        FoldG1 = FoldG#gnr{
          low_link=min(FoldG#gnr.low_link, AdjIndex)
        },
        FoldT#tarjan{map=FoldMap#{V := FoldG1}};

      true -> FoldT
    end
  end, T1, G#gnr.deps),

  #tarjan{stack=Stack2, map=Map2, solver=S2} = T2,
  #{V := G2} = Map2,
  if
    G2#gnr.low_link == G2#gnr.index ->
      {Popped, Left} = lists:splitwith(fun(StackV) ->
        StackV /= V
      end, Stack2),
      SolvableVs = [V | Popped],

      Map3 = lists:foldl(fun(SolV, FoldMap) ->
        #{SolV := SolG} = FoldMap,
        FoldMap#{SolV := SolG#gnr{on_stack=false}}
      end, Map2, SolvableVs),

      ?LOG("Solvable Vs", SolvableVs),

      S3 = lists:foldl(fun(SolV, FoldS) ->
        #{SolV := SolG} = Map3,
        unify_csts(SolG, FoldS)
      %% end, S2, SolvableVs),
      % TODO remove when done
      end, S2, lists:reverse(SolvableVs)),

      ?LOG("Subs", S3#solver.subs),

      S4 = lists:foldl(fun(SolV, FoldS) ->
        #{SolV := SolG} = Map3,
        Schemes = FoldS#solver.schemes,
        T = subs({tv, SolV, none, false}, FoldS#solver.subs),
        Schemes1 = Schemes#{SolV => generalize(T, SolG#gnr.env)},
        FoldS#solver{schemes=Schemes1}
      end, S3, SolvableVs),

      T2#tarjan{stack=tl(Left), map=Map3, solver=S4};

    true -> T2
  end.

unify_csts(#gnr{csts=Csts, env=Env}, S) ->
  RigidVs = maps:fold(fun(_, Value, FoldVs) ->
    case Value of
      {no_dep, T} -> gb_sets:union(FoldVs, fvs(T));
      {add_dep, _} -> FoldVs
    end
  end, gb_sets:new(), Env),

  lists:foldl(fun({L, R}, FoldS) ->
    Subs = FoldS#solver.subs,
    L1 = subs(resolve(L, FoldS), Subs),
    R1 = subs(resolve(R, FoldS), Subs),
    unify({L1, R1}, FoldS)
  end, S#solver{rigid_vs=RigidVs}, Csts).

resolve({lam, ArgT, ReturnT}, S) ->
  {lam, resolve(ArgT, S), resolve(ReturnT, S)};
resolve({tuple, LeftT, RightT}, S) ->
  {tuple, resolve(LeftT, S), resolve(RightT, S)};
resolve({tv, V, I, All}, _) -> {tv, V, I, All};
resolve({con, Con}, _) -> {con, Con};
resolve({gen, Con, ParamT}, S) -> {gen, Con, resolve(ParamT, S)};
resolve({inst, TV}, S) ->
  {tv, V, _, _} = TV,
  ResolvedT = case maps:find(V, S#solver.schemes) of
    {ok, Scheme} -> inst(Scheme, S);
    % Not sure if we should resolve() or not here to make inst vars rigid.
    error -> TV
  end,
  resolve(ResolvedT, S);
resolve(none, _) -> none.

inst({GVs, T}, S) ->
  Subs = gb_sets:fold(fun(V, FoldSubs) ->
    FoldSubs#{V => tv_server:next_name(S#solver.pid)}
  end, #{}, GVs),
  subs(T, Subs).

generalize(T, Env) ->
  EnvFVs = maps:fold(fun(_, {_, TV}, S) ->
    gb_sets:union(fvs(TV), S)
  end, gb_sets:new(), Env),

  GVs = gb_sets:subtract(fvs(T), EnvFVs),
  {GVs, T}.

unify({T1, T2}, S) when T1 == T2 -> S;

unify({{lam, ArgT1, ReturnT1}, {lam, ArgT2, ReturnT2}}, S) ->
  S1 = unify({ArgT1, ArgT2}, S),
  ToUnify = {subs(ReturnT1, S1#solver.subs), subs(ReturnT2, S1#solver.subs)},
  unify(ToUnify, S1);
unify({{tuple, LeftT1, RightT1}, {tuple, LeftT2, RightT2}}, S) ->
  S1 = unify({LeftT1, LeftT2}, S),
  ToUnify = {subs(RightT1, S1#solver.subs), subs(RightT2, S1#solver.subs)},
  unify(ToUnify, S1);

unify({{tv, V, I1, All1}, {tv, V, I2, All2}}, _) ->
  error({badarg, V, I1, All1, I2, All2});
unify({{tv, V1, I1, All1}, {tv, V2, I2, All2}}, S) ->
  TV1 = {tv, V1, I1, All1},
  TV2 = {tv, V2, I2, All2},

  Kind1 = kind(TV1, S),
  Kind2 = kind(TV2, S),
  Occurs = occurs(V1, TV2),

  if
    Occurs -> add_err({TV1, TV2}, S);

    % any(X: I1) ~ rigid(Y: I2) or any(X: I1) ~ all(Y: I2) or
    % rigid(X: I1) ~ rigid(Y: I2) if I1 <= I2.
    (Kind1 == any) or ((Kind1 == rigid) and (Kind2 == rigid)),
    (I1 == none) or (I1 == I2) ->
      add_sub(V1, TV2, S);

    % rigid(X: I1) ~ any(Y: I2) or all(X: I1) ~ rigid(Y: I2) or
    % rigid(X: I1) ~ rigid(Y: I2) if I1 >= I2.
    (Kind2 == any) or ((Kind1 == rigid) and (Kind2 == rigid)),
    (I2 == none) or (I1 == I2) ->
      add_sub(V2, TV1, S);

    % any(X: I) ~ rigid(Y) so long as we convert both to rigid(Y: I).
    % Note we must keep the same rigid type variable name Y.
    Kind1 == any, Kind2 == rigid, I2 == none ->
      add_sub(V2, {set_iface, I1}, add_sub(V1, TV2, S));

    % rigid(X) ~ any(Y: I) so long as we convert both to rigid(X: I).
    % Note we must keep the same rigid type variable name X.
    Kind2 == any, Kind1 == rigid, I1 == none ->
      add_sub(V1, {set_iface, I2}, add_sub(V2, TV1, S));

    true -> add_err({TV1, TV2}, S)
  end;
unify({{tv, V, I, All}, T}, S) ->
  TV = {tv, V, I, All},
  Kind = kind(TV, S),

  Err = {TV, T},
  Occurs = occurs(V, T),
  Instance = (I == none) or instance(T, I),
  HasTV = occurs(any, T),

  if
    Occurs -> add_err(Err, S);
    Kind == all -> add_err(Err, S);
    (Kind == rigid) and HasTV -> add_err(Err, S);
    Instance -> add_sub(V, T, S);
    true -> add_err(Err, S)
  end;
unify({T, {tv, V, I, All}}, S) -> unify({{tv, V, I, All}, T}, S);

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

kind({tv, V, _, All}, S) ->
  case gb_sets:is_member(V, S#solver.rigid_vs) of
    true ->
      false = All,
      rigid;
    false ->
      case All of
        true -> all;
        false -> any
      end
  end.

instance({con, 'Int'}, 'Num') -> true;
instance({con, 'Float'}, 'Num') -> true;
instance({con, 'String'}, 'Concatable') -> true;
instance({gen, 'List', _}, 'Concatable') -> true;
instance({gen, 'Map', _}, 'Concatable') -> true;
instance({gen, 'Set', _}, 'Concatable') -> true;
instance({gen, 'List', _}, 'Separable') -> true;
instance({gen, 'Set', _}, 'Separable') -> true;
instance(_, _) -> false.

subs({lam, ArgT, ReturnT}, Subs) ->
  {lam, subs(ArgT, Subs), subs(ReturnT, Subs)};
subs({tuple, LeftT, RightT}, Subs) ->
  {tuple, subs(LeftT, Subs), subs(RightT, Subs)};
subs({tv, V, I, All}, Subs) ->
  case maps:find(V, Subs) of
    error -> {tv, V, I, All};
    {ok, {all, V1}} -> {tv, V1, I, true};
    {ok, {set_iface, I1}} ->
      false = All,
      {tv, V, I1, All};

    {ok, Value} ->
      Sub = if
        % Replacing with a new type entirely
        is_tuple(Value) or (Value == none) -> Value;
        % Changing name due to instantiation; all flag is unset.
        true -> {tv, Value, I, false}
      end,
      subs(Sub, Subs)
  end;
subs({con, Con}, _) -> {con, Con};
subs({gen, Con, ParamT}, Subs) -> {gen, Con, subs(ParamT, Subs)};
subs({inst, TV}, Subs) -> {inst, subs(TV, Subs)};
subs(none, _) -> none.

fvs({lam, ArgT, ReturnT}) -> gb_sets:union(fvs(ArgT), fvs(ReturnT));
fvs({tuple, LeftT, RightT}) -> gb_sets:union(fvs(LeftT), fvs(RightT));
fvs({tv, V, _, _}) -> gb_sets:from_list([V]);
fvs({con, _}) -> gb_sets:new();
fvs({gen, _, ParamT}) -> fvs(ParamT);
% fvs({inst, ...}) ommitted; they should be resolved
fvs(none) -> gb_sets:new().

occurs(V, {lam, ArgT, ReturnT}) ->
  occurs(V, ArgT) or occurs(V, ReturnT);
occurs(V, {tuple, LeftT, RightT}) ->
  occurs(V, LeftT) or occurs(V, RightT);
occurs(V, {tv, V1, _, _}) -> (V == any) or (V == V1);
occurs(_, {con, _}) -> false;
occurs(V, {gen, _, ParamT}) -> occurs(V, ParamT);
% occurs({inst, ...}) ommitted; they should be resolved
occurs(_, none) -> false.

pretty_csts([]) -> [];
pretty_csts([{L, R} | Rest]) ->
  [{pretty(L), pretty(R)} | pretty_csts(Rest)].

pretty({lam, ArgT, ReturnT}) ->
  Format = case ArgT of
    {lam, _, _} -> "(~s) -> ~s";
    _ -> "~s -> ~s"
  end,
  format_str(Format, [pretty(ArgT), pretty(ReturnT)]);
pretty({tuple, LeftT, RightT}) ->
  format_str("(~s, ~s)", [pretty(LeftT), pretty_strip_parens(RightT)]);
pretty({tv, V, I, _}) ->
  VStr = if
    I == none -> tl(V);
    true -> format_str("~s: ~s", [tl(V), atom_to_list(I)])
  end,
  VStr;

  % TODO: how to deal with this?
  %% Size = gb_sets:size(GVs),
  %% if
  %%   Size > 0 ->
  %%     GVList = lists:map(fun erlang:tl/1, gb_sets:to_list(GVs)),
  %%     format_str("for all ~s, ~s", [string:join(GVList, " "), VStr]);
  %%   true -> format_str("~s", [VStr])
  %% end;
pretty({con, Con}) -> atom_to_list(Con);
pretty({gen, 'List', ParamT}) ->
  format_str("[~s]", [pretty_strip_parens(ParamT)]);
pretty({gen, T, ParamT}) ->
  format_str("~s<~s>", [atom_to_list(T), pretty_strip_parens(ParamT)]);
pretty({inst, TV}) ->
  format_str("inst(~s)", [pretty(TV)]);
pretty(none) -> "()".

pretty_strip_parens({tuple, LeftT, RightT}) ->
  format_str("~s, ~s", [pretty(LeftT), pretty(RightT)]);
pretty_strip_parens(T) -> pretty(T).

format_str(Str, Args) ->
  lists:flatten(io_lib:format(Str, Args)).
