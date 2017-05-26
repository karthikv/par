-module(par).
-export([reload/1, infer_prg/1, pretty/1, pattern_names/1]).

% Naming conventions:
%
% TV - a type variable, represented as a 4-tuple {tv, V, I, Cat}:
%   V - the variable name
%   I - the interface (typeclass) constraining the type variable
%   Cat - the category of type variable (any or all)
%
% T - a type, represented as a tuple:
%   {con, C} - a concrete type C; e.g. Int
%   {gen, G, T} - a generic type G<T>; e.g. List<String>
%   {tuple, L, R} - a tuple type (L, R); e.g. (Int, Bool)
%   {lam, X, Y} - a lambda type X -> Y; e.g. Int -> Bool
%   TV - see explanation above
%
% fresh - a function that generates a new TV.
% fvs - a function that computes the set of free TV names in an expression.
% Scheme - a tuple {GVs, T} that represents a T generalized across GVs, a set of
%          TV names.
% Env - a Name => T mapping of bindings in the environment.

% C - A context record for type inference with the following fields:
%   gnr - the current gnr record that constraints are being added to; see G
%         below
%   gnrs - an array of finalized gnr records that need to be solved
%   env - see Env above
%   types - a Name => TypeInfo mapping of types in the environment
%   pid - the process id of the TV server used to generated fresh TVs
-record(ctx, {gnr, gnrs, env, types, pid}).

% S - a solver record used to unify types and solve constraints
%   subs - the substitutions made to unify types
%   errs - any constraints that couldn't be unified
%   schemes - the schemes of env variables that have been solved for and
%             generalized
%   rigid_vs - the set of TV names in the environment
%   types - a Name => TypeInfo mapping of types in the environment
%   pid - the process id of the TV server used to generated fresh TVs
-record(solver, {subs, errs, schemes, rigid_vs, types, pid}).

% G - a gnr record that represents a set of constraints to solve before
%     generalizing a type variable:
%   v - the TV name to generalize
%   env - see Env above
%   csts - an array of constraints to solve before generalizing
%   deps - an array of TV names corresponding to gnr records that need to
%          solved before this record or, in the case of (mutual) recursion,
%          simultaneously with this record
%   index / low_link / on_stack - bookkeeping for Tarjan's strongly connected
%                                 components algorithm; see T below and [1]
-record(gnr, {
  id,
  vs,
  env,
  csts,
  deps,
  index,
  low_link,
  on_stack
}).

% T - A tarjan record that's used to apply Tarjan's strongly connected
%     components algorithm. This is necessary to solve constraints in the proper
%     order so as to respect dependencies.
%   map - a V => gnr record mapping so you can find the appropriate node given
%         the TV name
%   stack / next_index - bookkeeping for Tarjan's algorithm; see [1]
%   solver - the solver record used for unification; see S below
%
% [1] https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm
-record(tarjan, {stack, map, next_index, solver}).

-ifdef(release).
  -define(LOG(Prefix, Value), true).
-else.
  -define(
    LOG(Prefix, Value),
    io:format("~n(~p:~p) ~s:~n~p~n", [?MODULE, ?LINE, Prefix, Value])
  ).
-endif.

% TODO:
% - TODOs in code (non-unification error cases)
% - Error messages
% - Exhaustive pattern matching errors
% - Imports
% - Typeclasses + generics w/o concrete types (HKTs)
% - Concurrency
% - Exceptions
% - Code generation
% - Update naming conventions
%
% - + instead of ++ and - instead of --?
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
  ?LOG("AST", Ast),
  {ok, Pid} = tv_server:start_link(),

  C = #ctx{
    gnr=undefined,
    gnrs=[],
    env=#{},
    types=#{},
    pid=Pid
  },

  C1 = lists:foldl(fun(Node, FoldC) ->
    case Node of
      {global, {var, _, Name}, _} ->
        % TODO: what if name already exists?
        {TV, ID} = tv_server:fresh_gnr_id(FoldC#ctx.pid),
        add_env(Name, {add_dep, TV, ID}, FoldC);

      % TODO: register valid type for each enum/struct

      _ -> FoldC
    end
  end, C, Ast),

  C2 = lists:foldl(fun(Node, FoldC) ->
    case Node of
      {N, _, _} when N == enum; N == struct ->
        {_, FoldC1} = infer(Node, FoldC),
        FoldC1;

      _ -> FoldC
    end
  end, C1, Ast),

  {_, _, C3} = lists:foldl(fun(Node, {ExpName, SigT, FoldC}) ->
    if
      % TODO: handle error
      ExpName /= none -> {global, {var, _, ExpName}, _} = Node;
      true -> none
    end,

    case Node of
      {global, {var, _, Name}, Expr} ->
        #{Name := {add_dep, TV, ID}} = FoldC#ctx.env,
        % TODO: should anything be in this map?
        FoldC1 = new_gnr(TV, ID, FoldC),
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
  end, {none, none, C2}, Ast),

  S = #solver{
    subs=#{},
    errs=[],
    schemes=#{},
    types=C3#ctx.types,
    pid=Pid
  },

  Result = case solve(C3#ctx.gnrs, S) of
    {ok, Schemes} ->
      SubbedEnv = maps:map(fun(_, Value) ->
        {tv, V, _, _} = case Value of
          {no_dep, TV} -> TV;
          {add_dep, TV, _} -> TV
        end,
        inst(maps:get(V, Schemes), Pid)
      end, C3#ctx.env),
      {ok, SubbedEnv, Ast};
    {errors, Errs} -> {errors, Errs}
  end,

  ok = tv_server:stop(Pid),
  Result.

infer({fn, Args, Expr}, C) ->
  {ArgTsRev, C1} = lists:foldl(fun({var, _, ArgName}, {Ts, FoldC}) ->
    ArgTV = tv_server:fresh(FoldC#ctx.pid),
    {[ArgTV | Ts], add_env(ArgName, {no_dep, ArgTV}, FoldC)}
  end, {[], C}, Args),

  {ReturnT, C2} = infer(Expr, C1),
  T = if
    length(Args) == 0 -> {lam, none, ReturnT};
    true -> lists:foldl(fun(ArgT, LastT) ->
      {lam, ArgT, LastT}
    end, ReturnT, ArgTsRev)
  end,

  % restore original env
  {T, C2#ctx{env=C#ctx.env}};

infer({sig, _, Sig}, C) ->
  {SigT, C1} = infer(Sig, C),
  {norm_sig_type(SigT, [], C#ctx.pid), C1};

infer({expr_sig, Expr, Sig}, C) ->
  G = C#ctx.gnr,
  {TV, ID} = tv_server:fresh_gnr_id(C#ctx.pid),

  {ExprT, C1} = infer(Expr, new_gnr(TV, ID, C)),
  {SigT, C2} = infer(Sig, C1),
  NormSigT = norm_sig_type(SigT, [], C2#ctx.pid),

  C3 = add_csts([{TV, ExprT}, {TV, NormSigT}], C2),
  % TODO: make deps a set
  {{inst, TV}, finish_gnr(C3, G#gnr{deps=[ID | G#gnr.deps]})};

infer({lam_te, ArgTE, ReturnTE}, C) ->
  {ArgT, C1} = infer(ArgTE, C),
  {ReturnT, C2} = infer(ReturnTE, C1),
  {{lam, ArgT, ReturnT}, C2};
infer({tuple_te, LeftTE, RightTE}, C) ->
  {LeftT, C1} = infer(LeftTE, C),
  {RightT, C2} = infer(RightTE, C1),
  {{tuple, LeftT, RightT}, C2};
infer({iface_te, TVToken, TE}, C) ->
  % TODO: records in signatures
  {{tv, V, none, Cat}, C1} = infer(TVToken, C),
  case infer(TE, C1) of
    % TODO: ensure this is a valid iface
    {{con, I}, C2} -> {{tv, V, I, Cat}, C2};
    {{record, _, FieldMap}, C2} -> {{tv, V, FieldMap, Cat}, C2}
  end;
infer({gen_te, {con_token, _, Name}, ParamTE}, C) ->
  {ParamT, C1} = infer(ParamTE, C),
  {{gen, list_to_atom(Name), ParamT}, C1};
infer({tv_token, _, Name}, C) ->
  % This TV should be in category all, but because it's renamed in
  % norm_sig_type, it's reset to category any. Hence, we don't set category all
  % here. Rather, after renaming in norm_sig_type, we change to category all.
  {{tv, Name, none, any}, C};
% TODO: ensure these types are valid except when creating a new type
infer({con_token, _, Name}, C) -> {{con, list_to_atom(Name)}, C};
infer({record_te, Fields}, C) ->
  % TODO: ensure no name conflicts
  {FieldMap, C1} = lists:foldl(fun({Var, FieldTE}, {FoldMap, FoldC}) ->
    {var, _, Name} = Var,
    {FieldT, FoldC1} = infer(FieldTE, FoldC),
    {FoldMap#{Name => FieldT}, FoldC1}
  end, {#{}, C}, Fields),

  {{record, tv_server:next_name(C1#ctx.pid), FieldMap}, C1};

infer({enum, EnumTE, Options}, C) ->
  {T, C1} = infer(EnumTE, C),
  FVs = fvs(T),

  C2 = lists:foldl(fun({option, {con_token, _, Name}, ArgTEs}, FoldC) ->
    {ArgTsRev, FoldC1} = lists:foldl(fun(ArgTE, {Ts, InnerC}) ->
      {ArgT, InnerC1} = infer(ArgTE, InnerC),
      {[ArgT | Ts], InnerC1}
    end, {[], FoldC}, ArgTEs),

    OptionT = lists:foldl(fun(ArgT, LastT) ->
      {lam, ArgT, LastT}
    end, T, ArgTsRev),

    % TODO: handle error
    true = gb_sets:is_empty(gb_sets:difference(fvs(OptionT), FVs)),

    % don't need to exclude params; all(X) becomes any(X) during instantiation
    NormOptionT = norm_sig_type(OptionT, [], C#ctx.pid),

    % TODO: what if name already exists?
    {TV, ID} = tv_server:fresh_gnr_id(C#ctx.pid),
    FoldC2 = add_csts({TV, NormOptionT}, new_gnr(TV, ID, FoldC1)),
    add_env(Name, {add_dep, TV, ID}, finish_gnr(FoldC2, FoldC1#ctx.gnr))
  end, C1, Options),

  {T, C2};

infer({struct, StructTE, Fields}, C) ->
  {T, C1} = infer(StructTE, C),
  {{record, _, RawFieldMap}, C2} = infer({record_te, Fields}, C1),

  FieldFVs = fvs({record, none, RawFieldMap}),
  % TODO: handle error
  true = gb_sets:is_empty(gb_sets:difference(FieldFVs, fvs(T))),

  FnT = lists:foldr(fun({{var, _, Name}, _}, LastT) ->
    #{Name := FieldT} = RawFieldMap,
    {lam, FieldT, LastT}
  end, T, Fields),

  % don't need to exclude params; all(x) becomes any(X) during instantiation
  NormFnT = norm_sig_type(FnT, [], C2#ctx.pid),

  % TODO: should we have a separate types map or just use env?
  Types = C2#ctx.types,
  {StructCon, Value} = case T of
    {con, Con} -> {Con, {T, [], RawFieldMap}};
    {gen, Con, ParamT} ->
      Params = param_type_to_list(ParamT),
      Vs = lists:map(fun({tv, V, none, _}) -> V end, Params),
      {Con, {T, Vs, RawFieldMap}}
  end,

  % TODO: ensure reptitions of same tv have the same iface

  {TV, ID} = tv_server:fresh_gnr_id(C2#ctx.pid),
  C3 = add_env(atom_to_list(StructCon), {add_dep, TV, ID}, C2),
  C4 = new_gnr(TV, ID, C3#ctx{types=Types#{StructCon => Value}}),
  C5 = finish_gnr(add_csts({TV, NormFnT}, C4), C3#ctx.gnr),
  {TV, C5};

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

% only occurs when pattern matching to destructure list into head/tail
infer({list, Elems, Rest}, C) ->
  {T, C1} = infer({list, Elems}, C),
  {RestT, C2} = infer(Rest, C1),
  {T, add_csts({T, RestT}, C2)};

infer({tuple, Left, Right}, C) ->
  {LeftT, C1} = infer(Left, C),
  {RightT, C2} = infer(Right, C1),
  {{tuple, LeftT, RightT}, C2};

infer({map, Pairs}, C) ->
  KeyTV = tv_server:fresh(C#ctx.pid),
  ValueTV = tv_server:fresh(C#ctx.pid),

  {Csts, C1} = lists:foldl(fun({Key, Value}, {FoldCsts, FoldC}) ->
    {KeyT, FoldC1} = infer(Key, FoldC),
    {ValueT, FoldC2} = infer(Value, FoldC1),
    {[{KeyT, KeyTV}, {ValueT, ValueTV} | FoldCsts], FoldC2}
  end, {[], C}, Pairs),

  {{gen, 'Map', {tuple, KeyTV, ValueTV}}, add_csts(Csts, C1)};

infer({var, _, Name}, C) -> lookup(Name, C);
infer({con_var, _, Name}, C) -> lookup(Name, C);
% only occurs when pattern matching to designate a non-literal variable
infer({var_value, _, Name}, C) -> lookup(Name, C);

% only occurs when pattern matching to designate anything
infer({'_', _}, C) -> {tv_server:fresh(C#ctx.pid), C};

infer({record, Inits}, C) ->
  {FieldMap, C1} = lists:foldl(fun(Init, {Map, FoldC}) ->
    {{var, _, Name}, Expr} = Init,
    {T, FoldC1} = infer(Expr, FoldC),
    % TODO: handle name conflicts
    {Map#{Name => T}, FoldC1}
  end, {#{}, C}, Inits),

  {{record, tv_server:next_name(C#ctx.pid), FieldMap}, C1};

infer({update_record, Expr, Inits}, C) ->
  {ExprT, C1} = infer(Expr, C),
  {{record, _, FieldMap}, C2} = infer({record, Inits}, C1),

  RecordTV = tv_server:fresh(FieldMap, C2#ctx.pid),
  TV = tv_server:fresh(C2#ctx.pid),
  {TV, add_csts([{TV, ExprT}, {TV, RecordTV}], C2)};

infer({record, {con_var, _, Name}, Inits}, C) ->
  G = C#ctx.gnr,
  {TV, ID} = tv_server:fresh_gnr_id(C#ctx.pid),
  {RecordT, C1} = infer({record, Inits}, new_gnr(TV, ID, C)),

  % TODO: what if con isn't in map?
  Con = list_to_atom(Name),
  #{Con := {StructT, Vs, _}} = C1#ctx.types,
  NormSigT = norm_sig_type(StructT, Vs, C1#ctx.pid),

  C2 = add_csts([{TV, RecordT}, {TV, NormSigT}], C1),
  {{inst, TV}, finish_gnr(C2, G#gnr{deps=[ID | G#gnr.deps]})};

infer({field, {var, _, Name}}, C) ->
  FieldTV = tv_server:fresh(C#ctx.pid),
  TV = tv_server:fresh(#{Name => FieldTV}, C#ctx.pid),
  {{lam, TV, FieldTV}, C};

infer({field, Expr, Var}, C) ->
  {ExprT, C1} = infer(Expr, C),
  {FieldT, C2} = infer({field, Var}, C1),
  TV = tv_server:fresh(C2#ctx.pid),
  {TV, add_csts({{lam, ExprT, TV}, FieldT}, C2)};

infer({app, Expr, Args}, C) ->
  {ArgTsRev, C1} = lists:foldl(fun(Arg, {Ts, FoldC}) ->
    {T, FoldC1} = infer(Arg, FoldC),
    {[T | Ts], FoldC1}
  end, {[], C}, Args),

  {ExprT, C2} = infer(Expr, C1),
  TV = tv_server:fresh(C2#ctx.pid),
  T = if
    length(ArgTsRev) == 0 -> {lam, none, TV};
    true ->
      lists:foldl(fun(ArgT, LastT) ->
        {lam, ArgT, LastT}
      end, TV, ArgTsRev)
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
  % TODO: ensure no pattern name overlap!
  {Gs, C1} = lists:mapfoldl(fun({Pattern, _}, FoldC) ->
    FoldC1 = with_pattern_env(Pattern, new_gnr(FoldC)),
    % save new gnr and revert it back to original
    {FoldC1#ctx.gnr, FoldC1#ctx{gnr=FoldC#ctx.gnr}}
  end, C, Inits),

  C2 = lists:foldl(fun({G, {Pattern, InitExpr}}, FoldC) ->
    {PatternT, FoldC1} = infer(Pattern, FoldC#ctx{gnr=G}),
    {InitExprT, FoldC2} = infer(InitExpr, FoldC1),
    FoldC3 = add_csts({PatternT, InitExprT}, FoldC2),
    finish_gnr(FoldC3, FoldC#ctx.gnr)
  end, C1, lists:zip(Gs, Inits)),

  {T, C3} = infer(Expr, C2),
  {T, C3#ctx{env=C#ctx.env}};

infer({{if_let, _}, {Pattern, Expr}, Then, Else}, C) ->
  C1 = with_pattern_env(Pattern, new_gnr(C)),
  {PatternT, C2} = infer(Pattern, C1),
  {ExprT, C3} = infer(Expr, C2),
  C4 = add_csts({PatternT, ExprT}, C3),
  {ThenT, C5} = infer(Then, finish_gnr(C4, C#ctx.gnr)),

  case Else of
    none -> {none, C5};
    _ ->
      % must use original env without pattern bindings
      {ElseT, C6} = infer(Else, C5#ctx{env=C#ctx.env}),
      TV = tv_server:fresh(C#ctx.pid),
      {TV, add_csts([{TV, ThenT}, {TV, ElseT}], C6)}
  end;

infer({{match, _}, Expr, Cases}, C) ->
  TV = tv_server:fresh(C#ctx.pid),

  C1 = lists:foldl(fun({Pattern, Then}, FoldC) ->
    {ExprT, FoldC1} = infer(Expr, new_gnr(FoldC)),
    {PatternT, FoldC2} = infer(Pattern, with_pattern_env(Pattern, FoldC1)),
    FoldC3 = add_csts({ExprT, PatternT}, FoldC2),
    {ThenT, FoldC4} = infer(Then, finish_gnr(FoldC3, FoldC#ctx.gnr)),

    % revert env to before pattern was parsed
    add_csts([{TV, ThenT}], FoldC4#ctx{env=FoldC#ctx.env})
  end, C, Cases),

  {TV, C1};

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
    Op == '|>' ->
      ArgTV = tv_server:fresh(C2#ctx.pid),
      {
        {lam, LeftT, {lam, RightT, TV}},
        {lam, ArgTV, {lam, {lam, ArgTV, TV}, TV}}
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
    Op == '%' ->
      ReturnTV = tv_server:fresh('Num', C2#ctx.pid),
      {
        {lam, LeftT, {lam, RightT, TV}},
        {lam, {con, 'Int'}, {lam, {con, 'Int'}, ReturnTV}}
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

with_pattern_env(Pattern, C) ->
  ID = C#ctx.gnr#gnr.id,
  Names = pattern_names(Pattern),

  {Vs, C1} = gb_sets:fold(fun(Name, {FoldVs, FoldC}) ->
    TV = tv_server:fresh(C#ctx.pid),
    {tv, V, _, _} = TV,
    {[V | FoldVs], add_env(Name, {add_dep, TV, ID}, FoldC)}
  end, {[], C}, Names),

  C1#ctx{gnr=C1#ctx.gnr#gnr{vs=Vs}}.

pattern_names([]) -> gb_sets:new();
pattern_names([Node | Rest]) ->
  gb_sets:union(pattern_names(Node), pattern_names(Rest));
pattern_names({N, _, _}) when N == int; N == float; N == bool; N == str;
    N == atom; N == var_value; N == con_var ->
  gb_sets:new();
pattern_names({var, _, Name}) -> gb_sets:singleton(Name);
pattern_names({'_', _}) -> gb_sets:new();
pattern_names({app, ConVar, Args}) ->
  gb_sets:union(pattern_names(ConVar), pattern_names(Args));
pattern_names({list, List}) -> pattern_names(List);
pattern_names({list, List, Rest}) ->
  gb_sets:union(pattern_names(List), pattern_names(Rest));
pattern_names({tuple, Left, Right}) ->
  gb_sets:union(pattern_names(Left), pattern_names(Right)).

add_env(Name, Value, C) ->
  % just a sanity assertion that Value is in the right format
  case Value of
    {add_dep, {tv, _, _, _}, _} -> true;
    {no_dep, {tv, _, _, _}} -> true
  end,
  C#ctx{env=(C#ctx.env)#{Name => Value}}.

new_gnr(C) ->
  ID = tv_server:next_gnr_id(C#ctx.pid),
  G = #gnr{id=ID, vs=[], env=C#ctx.env, csts=[], deps=[]},
  C#ctx{gnr=G}.

new_gnr({tv, V, _, _}, ID, C) ->
  G = #gnr{id=ID, vs=[V], env=C#ctx.env, csts=[], deps=[]},
  C#ctx{gnr=G}.

finish_gnr(C, OldG) ->
  C#ctx{gnrs=[C#ctx.gnr | C#ctx.gnrs], gnr=OldG}.

add_csts(Csts, C) ->
  G = C#ctx.gnr,
  G1 = case is_list(Csts) of
    true -> G#gnr{csts=Csts ++ G#gnr.csts};
    false -> G#gnr{csts=[Csts | G#gnr.csts]}
  end,

  C#ctx{gnr=G1}.

norm_sig_type(SigT, ExceptVs, Pid) ->
  ExceptVsSet = gb_sets:from_list(ExceptVs),

  % TODO: is it more intuitive to change each fv to *fv and then replace?
  Subs = gb_sets:fold(fun(V, FoldSubs) ->
    case gb_sets:is_member(V, ExceptVsSet) of
      true -> FoldSubs#{V => tv_server:next_name(Pid)};
      false -> FoldSubs#{V => {all, tv_server:next_name(Pid)}}
    end
  end, #{}, fvs(SigT)),

  subs(SigT, Subs).

param_type_to_list({tuple, LeftT, RightT}) ->
  [LeftT | param_type_to_list(RightT)];
param_type_to_list(T) -> [T].

lookup(Name, C) ->
  % TODO: handle case where can't find variable
  case maps:find(Name, C#ctx.env) of
    {ok, {add_dep, EnvTV, ID}} ->
      G = C#ctx.gnr,
      G1 = G#gnr{deps=[ID | G#gnr.deps]},

      % We need to defer instantiation until we start solving constraints.
      % Otherwise, we don't know the real types of these variables, and can't
      % instantiate properly.
      {{inst, EnvTV}, C#ctx{gnr=G1}};

    {ok, {_, EnvTV}} -> {EnvTV, C}
  end.

solve(Gs, S) ->
  Map = lists:foldl(fun(G, FoldMap) -> FoldMap#{G#gnr.id => G} end, #{}, Gs),
  ?LOG("Gs", lists:map(fun(G) -> G#gnr{csts=pretty_csts(G#gnr.csts)} end, Gs)),

  T = lists:foldl(fun(#gnr{id=ID}, FoldT) ->
    #{ID := #gnr{index=Index}} = FoldT#tarjan.map,
    if
      Index == undefined -> connect(ID, FoldT#tarjan{stack=[]});
      true -> FoldT
    end
  end, #tarjan{map=Map, next_index=0, solver=S}, Gs),

  case T#tarjan.solver of
    #solver{errs=Errs} when length(Errs) > 0 -> {errors, Errs};
    #solver{schemes=Schemes} -> {ok, Schemes}
  end.

connect(ID, #tarjan{stack=Stack, map=Map, next_index=NextIndex, solver=S}) ->
  #{ID := G} = Map,
  Stack1 = [ID | Stack],
  Map1 = Map#{ID := G#gnr{index=NextIndex, low_link=NextIndex, on_stack=true}},

  T1 = #tarjan{stack=Stack1, map=Map1, next_index=NextIndex + 1, solver=S},
  T2 = lists:foldl(fun(AdjID, FoldT) ->
    #{AdjID := #gnr{index=AdjIndex, on_stack=AdjOnStack}} = FoldT#tarjan.map,

    if
      AdjIndex == undefined ->
        FoldT1 = connect(AdjID, FoldT),
        FoldMap1 = FoldT1#tarjan.map,
        #{ID := FoldG1, AdjID := AdjG1} = FoldMap1,
        FoldG2 = FoldG1#gnr{
          low_link=min(FoldG1#gnr.low_link, AdjG1#gnr.low_link)
        },
        FoldT1#tarjan{map=FoldMap1#{ID := FoldG2}};

      AdjOnStack ->
        FoldMap = FoldT#tarjan.map,
        #{ID := FoldG} = FoldMap,
        FoldG1 = FoldG#gnr{
          low_link=min(FoldG#gnr.low_link, AdjIndex)
        },
        FoldT#tarjan{map=FoldMap#{ID := FoldG1}};

      true -> FoldT
    end
  end, T1, G#gnr.deps),

  #tarjan{stack=Stack2, map=Map2, solver=S2} = T2,
  #{ID := G2} = Map2,
  if
    G2#gnr.low_link == G2#gnr.index ->
      {Popped, Left} = lists:splitwith(fun(StackID) ->
        StackID /= ID
      end, Stack2),
      SolvableIDs = [ID | Popped],

      Map3 = lists:foldl(fun(SolID, FoldMap) ->
        #{SolID := SolG} = FoldMap,
        FoldMap#{SolID := SolG#gnr{on_stack=false}}
      end, Map2, SolvableIDs),

      ?LOG("Solvable IDs", SolvableIDs),

      S3 = lists:foldl(fun(SolID, FoldS) ->
        #{SolID := SolG} = Map3,
        unify_csts(SolG, FoldS)
      end, S2, SolvableIDs),

      ?LOG("Subs", maps:map(fun(_, T) -> pretty(T) end, S3#solver.subs)),

      S4 = lists:foldl(fun(SolID, FoldS) ->
        #{SolID := SolG} = Map3,
        RigidVs = rigid_vs(SolG#gnr.env, FoldS),

        lists:foldl(fun(SolV, NestedS) ->
          #solver{subs=Subs, schemes=Schemes} = NestedS,
          SolTV = {tv, SolV, none, any},
          T = subs(SolTV, Subs),
          GVs = gb_sets:subtract(fvs(T), RigidVs),
          Schemes1 = Schemes#{SolV => {GVs, T}},
          NestedS#solver{schemes=Schemes1}
        end, FoldS, SolG#gnr.vs)
      end, S3, SolvableIDs),

      T2#tarjan{stack=tl(Left), map=Map3, solver=S4};

    true -> T2
  end.

unify_csts(#gnr{csts=Csts, env=Env}, S) ->
  % Constraints are always prepended to the list in a depth-first manner. Hence,
  % the shallowest expression's constraints come first. We'd like to solve the
  % deepest expression's constraints first to have better error messages (e.g.
  % rather than can't unify [A] with B, can't unify [Float] with Bool), so we
  % reverse the order here.
  OrderedCsts = lists:reverse(Csts),
  RigidVs = rigid_vs(Env, S),
  lists:foldl(fun({T1, T2}, FoldS) ->
    unify({resolve(T1, FoldS), resolve(T2, FoldS)}, FoldS)
  end, S#solver{rigid_vs=RigidVs}, OrderedCsts).

resolve({lam, ArgT, ReturnT}, S) ->
  {lam, resolve(ArgT, S), resolve(ReturnT, S)};
resolve({tuple, LeftT, RightT}, S) ->
  {tuple, resolve(LeftT, S), resolve(RightT, S)};
resolve({tv, V, I, Cat}, S) ->
  if
    is_map(I) ->
      NewI = maps:map(fun(_, T) -> resolve(T, S) end, I),
      {tv, V, NewI, Cat};
    true -> {tv, V, I, Cat}
  end;
resolve({con, Con}, _) -> {con, Con};
resolve({gen, Con, ParamT}, S) -> {gen, Con, resolve(ParamT, S)};
resolve({inst, TV}, S) ->
  {tv, V, _, _} = TV,
  ResolvedT = case maps:find(V, S#solver.schemes) of
    {ok, Scheme} -> inst(Scheme, S#solver.pid);
    error -> TV
  end,
  resolve(ResolvedT, S);
resolve({record, A, FieldMap}, S) ->
  {record, A, maps:map(fun(_, T) -> resolve(T, S) end, FieldMap)};
resolve(none, _) -> none.

inst({GVs, T}, Pid) ->
  Subs = gb_sets:fold(fun(V, FoldSubs) ->
    FoldSubs#{V => tv_server:next_name(Pid)}
  end, #{}, GVs),
  subs(T, Subs).

unify({T1, T2}, S) when T1 == T2 -> S;

unify({{lam, ArgT1, ReturnT1}, {lam, ArgT2, ReturnT2}}, S) ->
  S1 = unify({ArgT1, ArgT2}, S),
  % TODO: should we short-circuit this unification if args failed?
  unify({ReturnT1, ReturnT2}, S1);
unify({{tuple, LeftT1, RightT1}, {tuple, LeftT2, RightT2}}, S) ->
  S1 = unify({LeftT1, LeftT2}, S),
  unify({RightT1, RightT2}, S1);

unify({{record, A1, FieldMap1}, {record, A2, FieldMap2}}, S) ->
  Keys1 = gb_sets:from_list(maps:keys(FieldMap1)),
  Keys2 = gb_sets:from_list(maps:keys(FieldMap2)),

  if
    Keys1 /= Keys2 ->
      add_err({{record, A1, FieldMap1}, {record, A2, FieldMap2}}, S);

    true ->
      S1 = gb_sets:fold(fun(Key, FoldS) ->
        #{Key := T1} = FieldMap1,
        #{Key := T2} = FieldMap2,
        unify({T1, T2}, FoldS)
      end, S, Keys1),

      if
        (A1 == none) or (A2 == none) -> S1;
        length(S#solver.errs) == length(S1#solver.errs) ->
          add_sub(A1, {record, A2, FieldMap2}, S1);
        true -> S1
      end
  end;

unify({{tv, V1, I1, Cat1}, {tv, V2, I2, Cat2}}, S) ->
  TV1 = {tv, V1, I1, Cat1},
  TV2 = {tv, V2, I2, Cat2},

  case {subs(TV1, S#solver.subs), subs(TV2, S#solver.subs)} of
    {TV1, TV2} ->
      Ilk1 = ilk(TV1, S),
      Ilk2 = ilk(TV2, S),
      Occurs = occurs(V1, TV2) or occurs(V2, TV1),

      Err = {{tv, V1, I1, Ilk1}, {tv, V2, I2, Ilk2}},

      if
        Occurs -> add_err({TV1, TV2}, S);

        Ilk1 == any, Ilk2 == all ->
          case iface_lte(I1, I2, S) of
            false -> add_err(Err, S);
            S1 -> add_sub(V1, TV2, S1)
          end;

        Ilk2 == any, Ilk1 == all ->
          case iface_lte(I2, I1, S) of
            false -> add_err(Err, S);
            S1 -> add_sub(V2, TV1, S1)
         end;

        Ilk1 /= all, Ilk2 /= all ->
          CanKeepEither = ((Ilk1 == any) and (Ilk2 == any)) or
            ((Ilk1 == rigid) and (Ilk2 == rigid)),
          MustKeep1 = (Ilk1 == rigid) and (Ilk2 == any),
          MustKeep2 = (Ilk1 == any) and (Ilk2 == rigid),

          case iface_unify(I1, I2, S) of
            {I2, S1} when CanKeepEither; MustKeep2 -> add_sub(V1, TV2, S1);
            {I1, S1} when CanKeepEither; MustKeep1 -> add_sub(V2, TV1, S1);

            {NewI, S1} when CanKeepEither; MustKeep2 ->
              add_sub(V2, {set_iface, NewI}, add_sub(V1, TV2, S1));
            {NewI, S1} when CanKeepEither; MustKeep1 ->
              add_sub(V1, {set_iface, NewI}, add_sub(V2, TV1, S1));

            _ -> add_err(Err, S)
          end;

        true -> add_err(Err, S)
      end;

    {NewT1, NewT2} -> unify({NewT1, NewT2}, S)
  end;
unify({{tv, V, I, Cat}, T}, S) ->
  TV = {tv, V, I, Cat},
  case {subs(TV, S#solver.subs), subs(T, S#solver.subs)} of
    {TV, T} ->
      Ilk = ilk(TV, S),

      Err = {TV, T},
      Occurs = occurs(V, T),
      Instance = (I == none) or instance(T, I),
      HasTV = occurs(any, T),

      if
        Occurs -> add_err(Err, S);
        (Ilk == all) or ((Ilk == rigid) and HasTV) ->
          add_err({{tv, V, I, Ilk}, T}, S);

        Instance -> add_sub(V, T, S);
        is_map(I) ->
          case unalias(T, S) of
            {record, _, FieldMap} ->
              case iface_lte(I, FieldMap, S) of
                false -> add_err(Err, S);
                S1 -> add_sub(V, T, S1)
              end;
            T -> add_err(Err, S)
          end;

        true -> add_err(Err, S)
      end;

    {NewT1, NewT2} -> unify({NewT1, NewT2}, S)
  end;
unify({T, {tv, V, I, Cat}}, S) -> unify({{tv, V, I, Cat}, T}, S);

unify({{gen, Con, ParamT1}, {gen, Con, ParamT2}}, S) ->
  unify({ParamT1, ParamT2}, S);

unify({T, {record, A, FieldMap}}, S) ->
  RecordT = {record, A, FieldMap},
  case unalias(T, S) of
    T -> add_err({T, RecordT}, S);
    NewT ->
      S1 = unify({NewT, RecordT}, S),
      if
        length(S#solver.errs) == length(S1#solver.errs) -> add_sub(A, T, S1);
        true -> S1
      end
  end;
unify({{record, A, FieldMap}, T}, S) -> unify({T, {record, A, FieldMap}}, S);

unify({T1, T2}, S) ->
  case {unalias(T1, S), unalias(T2, S)} of
    {T1, _} -> add_err({T1, T2}, S);
    {_, T2} -> add_err({T1, T2}, S);
    {NewT1, NewT2} -> unify({NewT1, NewT2}, S)
  end.

add_sub(Key, Value, S) ->
  case maps:find(Key, S#solver.subs) of
    error -> S#solver{subs=(S#solver.subs)#{Key => Value}};
    % we're allowed to override set_iface to another value
    {ok, {set_iface, _}} -> S#solver{subs=(S#solver.subs)#{Key => Value}};
    {ok, Existing} -> error({badarg, Key, Existing, Value})
  end.

add_err({L, R}, S) ->
  Subs = S#solver.subs,
  Err = {subs(L, Subs), subs(R, Subs)},
  S#solver{errs=[Err | S#solver.errs]}.

ilk({tv, V, _, Cat}, S) ->
  case gb_sets:is_member(V, S#solver.rigid_vs) of
    true ->
      any = Cat,
      rigid;
    false -> Cat
  end.

iface_lte(I1, I2, S) ->
  if
    I1 == none; I1 == I2 -> S;
    true ->
      case {I1, I2} of
        _ when is_map(I1) and is_map(I2) ->
          Keys1 = gb_sets:from_list(maps:keys(I1)),
          Keys2 = gb_sets:from_list(maps:keys(I2)),

          case gb_sets:is_subset(Keys1, Keys2) of
            true ->
              gb_sets:fold(fun(Key, FoldS) ->
                #{Key := T1} = I1,
                #{Key := T2} = I2,
                unify({T1, T2}, FoldS)
              end, S, Keys1);
            false -> false
          end;
        _ -> false
      end
  end.

iface_unify(I1, I2, S) ->
  if
    I1 == none -> {I2, S};
    I2 == none -> {I1, S};
    I1 == I2 -> {I1, S};
    true ->
      case {I1, I2} of
        _ when is_map(I1) and is_map(I2) ->
          {NewMap, S1} = maps:fold(fun(Name, T1, {FoldMap, FoldS}) ->
            FoldS1 = case maps:find(Name, I2) of
              {ok, T2} -> unify({T1, T2}, FoldS);
              error -> FoldS
            end,
            {FoldMap#{Name => T1}, FoldS1}
          end, {#{}, S}, I1),

          {NewI, S2} = maps:fold(fun(Name, T2, {FoldMap, FoldS}) ->
            FoldS1 = case maps:find(Name, I1) of
              {ok, T1} -> unify({T1, T2}, FoldS);
              error -> FoldS
            end,
            {FoldMap#{Name => T2}, FoldS1}
          end, {NewMap, S1}, I2),

          {NewI, S2};
        _ -> false
      end
  end.

unalias({con, Con}, S) ->
  case maps:find(Con, S#solver.types) of
    {ok, {_, [], RawFieldMap}} -> {record, none, RawFieldMap};
    error -> {con, Con}
  end;
unalias({gen, Con, ParamT}, S) ->
  case maps:find(Con, S#solver.types) of
    {ok, {_, Vs, RawFieldMap}} ->
      Subs = maps:from_list(lists:zip(Vs, param_type_to_list(ParamT))),
      subs({record, none, RawFieldMap}, Subs);
    error -> {gen, Con, ParamT}
  end;
unalias(T, _) -> T.

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
subs({tv, V, I, Cat}, Subs) ->
  SubI = if
    is_map(I) -> element(3, subs({record, none, I}, Subs));
    true -> I
  end,

  case maps:find(V, Subs) of
    error -> {tv, V, SubI, Cat};
    {ok, any} -> {tv, V, SubI, any};
    {ok, {all, V1}} -> {tv, V1, SubI, all};

    {ok, {set_iface, I1}} ->
      any = Cat,
      if
        is_map(I1) ->
          SubI1 = element(3, subs({record, none, I1}, Subs)),
          {tv, V, SubI1, Cat};
        true -> {tv, V, I1, Cat}
      end;

    {ok, Value} ->
      Sub = if
        % Replacing with a new type entirely
        is_tuple(Value) or (Value == none) -> Value;
        % Instantiation, so category resets to any
        true -> {tv, Value, SubI, any}
      end,
      subs(Sub, Subs)
  end;
subs({con, Con}, _) -> {con, Con};
subs({gen, Con, ParamT}, Subs) -> {gen, Con, subs(ParamT, Subs)};
subs({record, A, FieldMap}, Subs) ->
  case maps:find(A, Subs) of
    error ->
      NewFieldMap = maps:map(fun(_, T) -> subs(T, Subs) end, FieldMap),
      {record, A, NewFieldMap};
    {ok, T} -> T
  end;
subs(none, _) -> none.

rigid_vs(Env, S) ->
  #solver{subs=Subs, schemes=Schemes} = S,
  maps:fold(fun(_, Value, FoldVs) ->
    case Value of
      {no_dep, T} -> gb_sets:union(FoldVs, fvs(subs(T, Subs)));

      % 1) If a given other binding has been fully generalized already,
      %    we'll add the rigid type variables from its scheme.
      % 2) If a given other binding is currently being generalized,
      %    its TV can be generalized over, and so we shouldn't add it here.
      {add_dep, {tv, V, _, _}, _} ->
        case maps:find(V, Schemes) of
          {ok, {GVs, T}} ->
            gb_sets:union(FoldVs, gb_sets:difference(fvs(T), GVs));
          error -> FoldVs
        end
    end
  end, gb_sets:new(), Env).

fvs({lam, ArgT, ReturnT}) -> gb_sets:union(fvs(ArgT), fvs(ReturnT));
fvs({tuple, LeftT, RightT}) -> gb_sets:union(fvs(LeftT), fvs(RightT));
fvs({tv, V, I, _}) ->
  if
    is_map(I) -> gb_sets:add(V, fvs({record, none, I}));
    true -> gb_sets:singleton(V)
  end;
fvs({con, _}) -> gb_sets:new();
fvs({gen, _, ParamT}) -> fvs(ParamT);
% fvs({inst, ...}) ommitted; they should be resolved
fvs({record, _, FieldMap}) ->
  maps:fold(fun(_, T, S) ->
    gb_sets:union(S, fvs(T))
  end, gb_sets:new(), FieldMap);
fvs(none) -> gb_sets:new().

occurs(V, {lam, ArgT, ReturnT}) ->
  occurs(V, ArgT) or occurs(V, ReturnT);
occurs(V, {tuple, LeftT, RightT}) ->
  occurs(V, LeftT) or occurs(V, RightT);
occurs(V, {tv, V1, I, _}) ->
  OccursI = if
    is_map(I) -> occurs(V, {record, none, I});
    true -> false
  end,
  OccursI or (V == any) or (V == V1);
occurs(_, {con, _}) -> false;
occurs(V, {gen, _, ParamT}) -> occurs(V, ParamT);
% occurs({inst, ...}) ommitted; they should be resolved
occurs(V, {record, _, FieldMap}) ->
  maps:fold(fun(_, T, Occurs) ->
    Occurs or occurs(V, T)
  end, false, FieldMap);
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
pretty({tv, V, I, Ilk}) ->
  Str = if
    I == none -> tl(V);
    is_map(I) -> format_str("{ ~s | ~s }", [tl(V), pretty_field_map(I)]);
    true -> format_str("~s: ~s", [tl(V), atom_to_list(I)])
  end,

  case Ilk of
    any -> Str;
    rigid -> format_str("rigid(~s)", [Str]);
    all -> format_str("all(~s)", [Str])
  end;
pretty({set_iface, I}) ->
  Str = if
    is_map(I) -> pretty_field_map(I);
    true -> atom_to_list(I)
  end,
  format_str("I = ~s", [Str]);
pretty({con, Con}) -> atom_to_list(Con);
pretty({gen, 'List', ParamT}) ->
  format_str("[~s]", [pretty_strip_parens(ParamT)]);
pretty({gen, T, ParamT}) ->
  format_str("~s<~s>", [atom_to_list(T), pretty_strip_parens(ParamT)]);
pretty({inst, TV}) ->
  format_str("inst(~s)", [pretty(TV)]);
pretty({A, Options}) when A == either; A == ambig ->
  Strs = lists:map(fun(O) -> pretty(O) end, Options),
  format_str("~s(~s)", [atom_to_list(A), string:join(lists:sort(Strs), ", ")]);
pretty({record, _, FieldMap}) ->
  format_str("{ ~s }", [pretty_field_map(FieldMap)]);
pretty(none) -> "()".

pretty_strip_parens({tuple, LeftT, RightT}) ->
  format_str("~s, ~s", [pretty(LeftT), pretty_strip_parens(RightT)]);
pretty_strip_parens(T) -> pretty(T).

pretty_field_map(FieldMap) ->
  FieldStrs = maps:fold(fun(Name, T, Strs) ->
    [format_str("~s :: ~s", [Name, pretty(T)]) | Strs]
  end, [], FieldMap),
  string:join(lists:sort(FieldStrs), ", ").

format_str(Str, Args) ->
  lists:flatten(io_lib:format(Str, Args)).
