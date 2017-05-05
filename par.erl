-module(par).
-export([reload/1, infer_prg/1, subs/2, fvs/1, pretty/1]).

-record(ctx, {gnr, gnrs, env, pid}).
-record(solver, {subs, errs, schemes, pid}).

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
      {global, _, _} ->
        {_, FoldC1} = infer(Node, FoldC),
        %% Csts = if
        %%   SigT == none -> FoldC1#ctx.csts;
        %%   true -> [{TV, SigT} | FoldC1#ctx.csts]
        %% end,

        %% FoldC2 = FoldC1#ctx{csts=lists:reverse(Csts)},
        {none, none, FoldC1};

      %% {sig, {var, _, Name}, _} ->
      %%   {T, FoldC1} = infer(Node, FoldC#ctx{csts=[], deps=[]}),
      %%   {Name, T, GVCs, FoldC1};

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

infer({global, {var, _, Name}, Expr}, C) ->
  #{Name := {add_dep, TV}} = C#ctx.env,
  {T, C1} = infer(Expr, new_gnr(TV, C)),
  C2 = add_csts({TV, T}, C1),
  {TV, finish_gnr(C2, none)};

infer({fn, Args, Expr}, C) ->
  {ArgsTRev, C1} = lists:foldl(fun({var, _, ArgName}, {Ts, FoldC}) ->
    TV = tv_server:fresh(FoldC#ctx.pid),
    {[TV | Ts], add_env(ArgName, {no_dep, TV}, FoldC)}
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

infer({sig_expr, Expr, Sig}, C) ->
  {ExprT, C1} = infer(Expr, C),
  {SigT, C2} = infer(Sig, C1),

  NormSigT = norm_sig_type(SigT, C#ctx.pid),
  {ExprT, add_csts({ExprT, NormSigT}, C2)};

infer({lam_expr, Arg, Return}, C) ->
  {ArgT, C1} = infer(Arg, C),
  {ReturnT, C2} = infer(Return, C1),
  {{lam, ArgT, ReturnT}, C2};
infer({tuple_expr, Left, Right}, C) ->
  {LeftT, C1} = infer(Left, C),
  {RightT, C2} = infer(Right, C1),
  {{tuple, LeftT, RightT}, C2};
infer({iface_expr, TVToken, ConToken}, C) ->
  {{tv, V, none, GVs}, C1} = infer(TVToken, C),
  {{con, I}, C2} = infer(ConToken, C1),
  {{tv, V, I, GVs}, C2};
infer({gen_expr, ConToken, Param}, C) ->
  {{con, T}, C1} = infer(ConToken, C),
  {ParamT, C2} = infer(Param, C1),
  {{gen, T, ParamT}, C2};
infer({tv_token, _, Name}, C) -> {{tv, Name, none, gb_sets:new()}, C};
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
  NewFVList = lists:map(fun(_) -> tv_server:next_name(Pid) end, FVList),
  FVSubs = maps:from_list(lists:zip(FVList, NewFVList)),

  GVs = gb_sets:from_list(NewFVList),
  GVSubs = maps:from_list(lists:map(fun(FV) ->
    {FV, {add_gvs, GVs}}
  end, NewFVList)),

  subs(subs(SigT, FVSubs), GVSubs).

solve(Gs, S) ->
  Map = lists:foldl(fun(G, FoldMap) -> FoldMap#{G#gnr.v => G} end, #{}, Gs),

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
  %% io:format("running connect ~p~n", [V]),
  #{V := G} = Map,
  Stack1 = [V | Stack],
  Map1 = Map#{V := G#gnr{index=NextIndex, low_link=NextIndex, on_stack=true}},

  T1 = #tarjan{stack=Stack1, map=Map1, next_index=NextIndex + 1, solver=S},
  T2 = lists:foldl(fun(AdjV, FoldT) ->
    #{AdjV := #gnr{index=AdjIndex, on_stack=AdjOnStack}} = FoldT#tarjan.map,
    %% io:format("got ~p AdjIndex ~p AdjOnStack ~p~n", [AdjV, AdjIndex, AdjOnStack]),
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
      %% io:format("got remaining ~p~n", [Map3]),

      %% io:format("got solvable vs ~p~n", [SolvableVs]),
      Csts = lists:foldl(fun(SolV, FoldCsts) ->
        #{SolV := SolG} = Map3,
        SolG#gnr.csts ++ FoldCsts
      end, [], SolvableVs),

      S3 = lists:foldl(fun(SolV, FoldS) ->
        #{SolV := SolG} = Map3,
        Schemes = FoldS#solver.schemes,
        T = subs({tv, SolV, none, none}, FoldS#solver.subs),
        Schemes1 = Schemes#{SolV => generalize(T, SolG#gnr.env)},
        FoldS#solver{schemes=Schemes1}
      end, unify_csts(Csts, S2), SolvableVs),
      %% io:format("got slvr ~p~n", [S3]),

      T2#tarjan{stack=tl(Left), map=Map3, solver=S3};

    true -> T2
  end.

%% solve(GVCs, S) ->
%%   {Solvable, Unsolved} = lists:partition(fun({_, C}) ->
%%     length(C#ctx.deps) == 0
%%   end, GVCs),
%%
%%   if
%%     length(Solvable) == 0 ->
%%       % If all global contexts left have dependencies, that means each remaining
%%       % global variable either is (mutually) recursive or depends on another
%%       % variable that's (mutually) recursive. We solve all constraints
%%       % simultaneously to resolve these. Note that any {inst, ...} of these
%%       % variables won't be generalized because the corresponding type variables
%%       % are already in the env; we impose this non-polymorphic constraint to
%%       % infer types with recursion.
%%       Csts = lists:flatmap(fun({_, C}) -> C#ctx.csts end, Unsolved),
%%       ?LOG("Csts", pretty_csts(Csts)),
%%       S1 = unify_csts(Csts, S),
%%       solve([], S1);
%%
%%     true ->
%%       {Solved, S1} = lists:foldl(fun({TV, C}, {Solved, FoldS}) ->
%%         ?LOG("Csts", pretty_csts(C#ctx.csts)),
%%         FoldS1 = unify_csts(C#ctx.csts, FoldS),
%%         %% ?LOG("Subs", maps:to_list(FoldS1#solver.subs)),
%%         {gb_sets:add(TV, Solved), FoldS1}
%%       end, {gb_sets:new(), S}, Solvable),
%%
%%       Rest = if
%%         length(Solvable) == 0 -> [];
%%         true -> lists:map(fun({TV, C}) ->
%%           Deps = lists:filter(fun(Dep) ->
%%             not gb_sets:is_element(Dep, Solved)
%%           end, C#ctx.deps),
%%           {TV, C#ctx{deps=Deps}}
%%         end, Unsolved)
%%       end,
%%
%%       solve(Rest, S1)
%%   end.

unify_csts(Csts, S) ->
  lists:foldl(fun({L, R}, FoldS) ->
    Subs = FoldS#solver.subs,
    L1 = subs(resolve(L, FoldS), Subs),
    R1 = subs(resolve(R, FoldS), Subs),
    io:format("solving ~p~n", [{pretty(L1), pretty(R1)}]),
    unify({L1, R1}, FoldS)
  end, S, Csts).

resolve({lam, ArgT, ReturnT}, S) ->
  {lam, resolve(ArgT, S), resolve(ReturnT, S)};
resolve({tuple, LeftT, RightT}, S) ->
  {tuple, resolve(LeftT, S), resolve(RightT, S)};
resolve({tv, V, I, GVs}, _) -> {tv, V, I, GVs};
resolve({con, Con}, _) -> {con, Con};
resolve({gen, Con, ParamT}, _) -> {gen, Con, ParamT};
% TODO: rename {inst, T} to {inst, TV}
% TODO: remove GVs from {tv}
resolve({inst, T}, S) ->
  {tv, V, _, _} = T,
  Res = case maps:find(V, S#solver.schemes) of
    {ok, Scheme} -> inst(Scheme, S);
    error -> T
  end,
  io:format("inst(~p)~n => ~p~n", [T, Res]),
  Res;
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
  %% % TODO: can simply replace add_gvs set with a flag
  %% Subs = gb_sets:fold(fun(GV, FoldSubs) ->
  %%   FoldSubs#{GV => {add_gvs, GVs}}
  %% end, #{}, GVs),

  %% subs(T, Subs).

unify({T1, T2}, S) when T1 == T2 -> S;

unify({{lam, ArgT1, ReturnT1}, {lam, ArgT2, ReturnT2}}, S) ->
  S1 = unify({ArgT1, ArgT2}, S),
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

    % V2 is equally or more constraining; change V1 -> V2
    AllV1 == AllV2, I1 == I2; AllV1 == AllV2, I1 == none ->
      add_sub(V1, {tv, V2, I2, gb_sets:union(GVs2, GVs1)}, S);

    % V1 is equally or more constraining; change V1 -> V2
    AllV1 == AllV2, I2 == none ->
      add_sub(V2, {tv, V1, I1, gb_sets:union(GVs1, GVs2)}, S);

    % We're now guaranteed either:
    % (1) AllV1 /= AllV2
    % (2) I1 /= I2 and I1 /= none and I2 /= none
    %
    % We can't reconcile (1) because for all A. A is different from B.
    % We can't reconcile (2) because there are two opposing interfaces.
    % We're out of options.
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

subs({lam, ArgT, ReturnT}, Subs) ->
  {lam, subs(ArgT, Subs), subs(ReturnT, Subs)};
subs({tuple, LeftT, RightT}, Subs) ->
  {tuple, subs(LeftT, Subs), subs(RightT, Subs)};
subs({tv, V, I, GVs}, Subs) ->
  case maps:find(V, Subs) of
    error -> {tv, V, I, GVs};
    {ok, {add_gvs, NewGVs}} -> {tv, V, I, gb_sets:union(GVs, NewGVs)};

    {ok, Value} ->
      Sub = if
        % Replacing with a new type entirely
        is_tuple(Value) or (Value == none) -> Value;
        % Changing name due to instantiation; GVs don't carry over.
        true ->
          %% NewGVs = gb_sets:from_list(lists:map(fun(GV) ->
          %%   case maps:find(GV, Subs) of
          %%     {ok, Value} when not is_tuple(Value) and (Value /= none) -> Value;
          %%     _ -> GV
          %%   end
          %% end, gb_sets:to_list(GVs))),
          {tv, Value, I, gb_sets:new()}
      end,
      subs(Sub, Subs)
  end;
subs({con, Con}, _) -> {con, Con};
subs({gen, Con, ParamT}, Subs) -> {gen, Con, subs(ParamT, Subs)};
subs({inst, T}, Subs) -> {inst, subs(T, Subs)};
subs(none, _) -> none.

fvs({lam, ArgT, ReturnT}) -> gb_sets:union(fvs(ArgT), fvs(ReturnT));
fvs({tuple, LeftT, RightT}) -> gb_sets:union(fvs(LeftT), fvs(RightT));
fvs({tv, V, _, _}) -> gb_sets:from_list([V]);
fvs({con, _}) -> gb_sets:new();
fvs({gen, _, ParamT}) -> fvs(ParamT);
% fvs({inst/generalize, ...}) ommitted; they should be resolved
fvs(none) -> gb_sets:new().

gvs({lam, ArgT, ReturnT}) -> gb_sets:union(gvs(ArgT), gvs(ReturnT));
gvs({tuple, LeftT, RightT}) -> gb_sets:union(gvs(LeftT), gvs(RightT));
gvs({tv, V, _, GVs}) ->
  case gb_sets:is_member(V, GVs) of
    true -> gb_sets:from_list([V]);
    false -> gb_sets:new()
  end;
gvs({con, _}) -> gb_sets:new();
gvs({gen, _, ParamT}) -> gvs(ParamT);
% gvs({inst/generalize, ...}) ommitted; they should be resolved
gvs(none) -> gb_sets:new().

occurs(S, {lam, ArgT, ReturnT}) ->
  occurs(S, ArgT) or occurs(S, ReturnT);
occurs(S, {tuple, LeftT, RightT}) ->
  occurs(S, LeftT) or occurs(S, RightT);
occurs(S, {tv, V, _, GVs}) -> not gb_sets:is_disjoint(S, gb_sets:add(V, GVs));
occurs(_, {con, _}) -> false;
occurs(S, {gen, _, ParamT}) -> occurs(S, ParamT);
% occurs({inst/generalize, ...}) ommitted; they should be resolved
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
pretty({tv, V, I, GVs}) ->
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
pretty({inst, T}) ->
  format_str("inst(~s)", [pretty(T)]);
pretty(none) -> "()".

pretty_strip_parens({tuple, LeftT, RightT}) ->
  format_str("~s, ~s", [pretty(LeftT), pretty(RightT)]);
pretty_strip_parens(T) -> pretty(T).

format_str(Str, Args) ->
  lists:flatten(io_lib:format(Str, Args)).
