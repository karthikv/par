-module(par).
-export([reload/1, infer_prg/1, pretty/1, pattern_names/1]).
-include("errors.hrl").

% Naming conventions:
%
% TV - a type variable, represented as a 4-tuple {tv, V, I, Rigid}:
%   V - the variable name
%   I - the interface (typeclass) constraining the type variable
%   Rigid - whether the type variable is rigid
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
%   line - the line of the last inferred expression
%   pid - the process id of the TV server used to generated fresh TVs
-record(ctx, {gnr, gnrs, env, types, line, pid}).

% S - a solver record used to unify types and solve constraints
%   subs - the substitutions made to unify types
%   errs - any constraints that couldn't be unified
%   schemes - the schemes of env variables that have been solved for and
%             generalized
%   bound_vs - the set of TV names in the environment
%   types - a Name => TypeInfo mapping of types in the environment
%   line - the line of the current constraint that's being unified
%   from - a string describing where the current constraint is from
%   pid - the process id of the TV server used to generated fresh TVs
-record(solver, {subs, errs, schemes, bound_vs, types, line, from, pid}).

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
% - Simplify let/if-let type checking
% - Simplify tuple access
% - Rename compiler to code gen
% - (code gen) File name attribute?
% - (code gen) Remove util functions when they're unused
% - (code gen) Use a bag instead of a set for constants?
% - Simplify interpreter let/if-let and tuple access
%
% - Error messages
% - TODOs in code (non-unification error cases)
% - Pattern matching records
% - Imports
% - Typeclasses + generics w/o concrete types (HKTs)
% - Exceptions
% - Exhaustive pattern matching errors
% - Concurrency
% - Update naming conventions
%
% From dogfooding:
% - Syntax to prepend list element
% - Operation: nth element of tuple? Rethink tuple access
% - Character type and operations
% - List error messages should include full List type
% - Norm types for error messages
% - Interpreter backtraces
% - Detect basic infinite loop conditions
%
% - Syntax for lambda with no arg?
% - Force all block expressions except last to be type ()?
% - List indexing?

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
    line=undefined,
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
      {{N, _}, _, _} when N == enum_token; N == struct_token ->
        {_, FoldC1} = infer(Node, FoldC),
        FoldC1;

      _ -> FoldC
    end
  end, C1, Ast),

  {_, _, _, C3} = lists:foldl(fun(Node, {ExpName, SigT, SigLine, FoldC}) ->
    if
      % TODO: handle error
      ExpName /= none -> {global, {var, _, ExpName}, _} = Node;
      true -> none
    end,

    case Node of
      {global, {var, Line, Name}, Expr} ->
        #{Name := {add_dep, TV, ID}} = FoldC#ctx.env,
        % TODO: should anything be in this map?
        FoldC1 = new_gnr(TV, ID, FoldC),
        {T, FoldC2} = infer(Expr, FoldC1),
        FoldC3 = add_cst(TV, T, Line, ?FROM_GLOBAL_DEF, FoldC2),

        FoldC4 = if
          SigT == none -> FoldC3;
          true -> add_cst(TV, SigT, SigLine, ?FROM_GLOBAL_SIG, FoldC3)
        end,
        {none, none, none, finish_gnr(FoldC4, FoldC#ctx.gnr)};

      {sig, {var, Line, Name}, _} ->
        {T, FoldC1} = infer(Node, FoldC),
        {Name, T, Line, FoldC1};

      % we've already processed enums/structs
      _ -> {ExpName, SigT, SigLine, FoldC}
    end
  end, {none, none, none, C2}, Ast),

  S = #solver{
    subs=#{},
    errs=[],
    schemes=#{},
    types=C3#ctx.types,
    line=undefined,
    from=undefined,
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

infer({{fn, Line}, Args, Expr}, C) ->
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
  {T, set_line(Line, C2#ctx{env=C#ctx.env})};

infer({sig, _, Sig}, C) ->
  {SigT, C1} = infer(Sig, C),
  % set_line unnecessary; line used directly by infer_prg
  {norm_sig_type(SigT, [], C#ctx.pid), C1};

infer({{'::', Line}, Expr, Sig}, C) ->
  G = C#ctx.gnr,
  {TV, ID} = tv_server:fresh_gnr_id(C#ctx.pid),

  {ExprT, C1} = infer(Expr, new_gnr(TV, ID, C)),
  ExprLine = C1#ctx.line,
  % signatures don't set line, so we use the line from '::'
  % TODO: make signatures set line?
  {SigT, C2} = infer(Sig, C1),

  NormSigT = norm_sig_type(SigT, [], C2#ctx.pid),
  C3 = add_cst(TV, ExprT, ExprLine, ?FROM_EXPR_SIG, C2),
  C4 = add_cst(TV, NormSigT, Line, ?FROM_EXPR_SIG, C3),
  C5 = finish_gnr(C4, G#gnr{deps=[ID | G#gnr.deps]}),

  % TODO: make deps a set
  {{inst, TV}, set_line(ExprLine, C5)};

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
  {{tv, V, none, Rigid}, C1} = infer(TVToken, C),
  case infer(TE, C1) of
    % TODO: ensure this is a valid iface
    {{con, I}, C2} -> {{tv, V, I, Rigid}, C2};
    {{record, _, FieldMap}, C2} -> {{tv, V, FieldMap, Rigid}, C2}
  end;
infer({gen_te, {con_token, _, Name}, ParamTE}, C) ->
  {ParamT, C1} = infer(ParamTE, C),
  {{gen, list_to_atom(Name), ParamT}, C1};
infer({tv_token, _, Name}, C) ->
  % This TV should be rigid, but it'll be reset to flex in norm_sig_type.
  % Hence, we don't set rigid here, but rather after renaming.
  {{tv, Name, none, false}, C};
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

infer({{enum_token, _}, EnumTE, Options}, C) ->
  {T, C1} = infer(EnumTE, C),
  FVs = fvs(T),

  C2 = lists:foldl(fun({option, {con_token, Line, Name}, ArgTEs}, FoldC) ->
    {ArgTsRev, FoldC1} = lists:foldl(fun(ArgTE, {Ts, InnerC}) ->
      {ArgT, InnerC1} = infer(ArgTE, InnerC),
      {[ArgT | Ts], InnerC1}
    end, {[], FoldC}, ArgTEs),

    OptionT = lists:foldl(fun(ArgT, LastT) ->
      {lam, ArgT, LastT}
    end, T, ArgTsRev),

    % TODO: handle error
    true = gb_sets:is_empty(gb_sets:difference(fvs(OptionT), FVs)),

    % don't need to exclude params; rigid(X) becomes X during inst
    NormOptionT = norm_sig_type(OptionT, [], C#ctx.pid),

    % TODO: what if name already exists?
    {TV, ID} = tv_server:fresh_gnr_id(C#ctx.pid),
    FoldC2 = new_gnr(TV, ID, FoldC1),
    FoldC3 = add_cst(TV, NormOptionT, Line, ?FROM_ENUM_CTOR, FoldC2),
    add_env(Name, {add_dep, TV, ID}, finish_gnr(FoldC3, FoldC1#ctx.gnr))
  end, C1, Options),

  % set_line unnecessary; top-level declaration
  {T, C2};

infer({{struct_token, Line}, StructTE, Fields}, C) ->
  {T, C1} = infer(StructTE, C),
  {{record, _, RawFieldMap}, C2} = infer({record_te, Fields}, C1),

  FieldFVs = fvs({record, none, RawFieldMap}),
  % TODO: handle error
  true = gb_sets:is_empty(gb_sets:difference(FieldFVs, fvs(T))),

  FnT = lists:foldr(fun({{var, _, Name}, _}, LastT) ->
    #{Name := FieldT} = RawFieldMap,
    {lam, FieldT, LastT}
  end, T, Fields),

  % don't need to exclude params; rigid(x) becomes X during inst
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
  C5 = add_cst(TV, NormFnT, Line, ?FROM_STRUCT_CTOR, C4),
  C6 = finish_gnr(C5, C3#ctx.gnr),

  % set_line unnecessary; top-level declaration
  {TV, C6};

infer({none, Line}, C) -> {none, set_line(Line, C)};
infer({int, Line, _}, C) ->
  {tv_server:fresh('Num', C#ctx.pid), set_line(Line, C)};
infer({float, Line, _}, C) -> {{con, 'Float'}, set_line(Line, C)};
infer({bool, Line, _}, C) -> {{con, 'Bool'}, set_line(Line, C)};
infer({str, Line, _}, C) -> {{con, 'String'}, set_line(Line, C)};
infer({atom, Line, _}, C) -> {{con, 'Atom'}, set_line(Line, C)};

infer({{list, Line}, Elems}, C) ->
  TV = tv_server:fresh(C#ctx.pid),

  C1 = lists:foldl(fun(Elem, FoldC) ->
    {ElemT, FoldC1} = infer(Elem, FoldC),
    add_cst(ElemT, TV, FoldC1#ctx.line, ?FROM_LIST_ELEM, FoldC1)
  end, C, Elems),

  {{gen, 'List', TV}, set_line(Line, C1)};

% only occurs when pattern matching to destructure list into head/tail
infer({{list, Line}, Elems, Tail}, C) ->
  {T, C1} = infer({{list, Line}, Elems}, C),
  {TailT, C2} = infer(Tail, C1),
  C3 = add_cst(T, TailT, C2#ctx.line, ?FROM_LIST_TAIL, C2),
  {T, set_line(Line, C3)};

infer({{tuple, Line}, Left, Right}, C) ->
  {LeftT, C1} = infer(Left, C),
  {RightT, C2} = infer(Right, C1),
  {{tuple, LeftT, RightT}, set_line(Line, C2)};

infer({{map, Line}, Pairs}, C) ->
  KeyTV = tv_server:fresh(C#ctx.pid),
  ValueTV = tv_server:fresh(C#ctx.pid),

  C1 = lists:foldl(fun({Key, Value}, FoldC) ->
    {KeyT, FoldC1} = infer(Key, FoldC),
    FoldC2 = add_cst(KeyT, KeyTV, FoldC1#ctx.line, ?FROM_MAP_KEY, FoldC1),
    {ValueT, FoldC3} = infer(Value, FoldC2),
    add_cst(ValueT, ValueTV, FoldC3#ctx.line, ?FROM_MAP_VALUE, FoldC3)
  end, C, Pairs),

  {{gen, 'Map', {tuple, KeyTV, ValueTV}}, set_line(Line, C1)};

infer({N, Line, Name}, C) when N == var; N == con_var; N == var_value ->
  {T, C1} = lookup(Name, C),
  {T, set_line(Line, C1)};

% only occurs when pattern matching to designate anything
infer({'_', Line}, C) -> {tv_server:fresh(C#ctx.pid), set_line(Line, C)};

infer({{record, Line}, Inits}, C) ->
  {FieldMap, C1} = lists:foldl(fun(Init, {Map, FoldC}) ->
    {{var, _, Name}, Expr} = Init,
    {T, FoldC1} = infer(Expr, FoldC),
    % TODO: handle name conflicts
    {Map#{Name => T}, FoldC1}
  end, {#{}, C}, Inits),

  {{record, tv_server:next_name(C#ctx.pid), FieldMap}, set_line(Line, C1)};

infer({{update_record, Line}, Expr, Inits}, C) ->
  {ExprT, C1} = infer(Expr, C),
  {{record, _, FieldMap}, C2} = infer({{record, Line}, Inits}, C1),

  RecordTV = tv_server:fresh(FieldMap, C2#ctx.pid),
  TV = tv_server:fresh(C2#ctx.pid),

  C3 = add_cst(TV, ExprT, Line, ?FROM_RECORD_UPDATE, C2),
  C4 = add_cst(TV, RecordTV, Line, ?FROM_RECORD_UPDATE, C3),
  {TV, set_line(Line, C4)};

infer({{record, Line}, {con_var, _, Name}, Inits}, C) ->
  G = C#ctx.gnr,
  {TV, ID} = tv_server:fresh_gnr_id(C#ctx.pid),
  {RecordT, C1} = infer({{record, Line}, Inits}, new_gnr(TV, ID, C)),

  % TODO: what if con isn't in map?
  Con = list_to_atom(Name),
  #{Con := {StructT, Vs, _}} = C1#ctx.types,
  NormSigT = norm_sig_type(StructT, Vs, C1#ctx.pid),

  From = ?FROM_RECORD_CREATE(Name),
  C2 = add_cst(TV, RecordT, Line, From, C1),
  C3 = add_cst(TV, NormSigT, Line, From, C2),
  C4 = finish_gnr(C3, G#gnr{deps=[ID | G#gnr.deps]}),
  {{inst, TV}, set_line(Line, C4)};

infer({field, {var, Line, Name}}, C) ->
  FieldTV = tv_server:fresh(C#ctx.pid),
  TV = tv_server:fresh(#{Name => FieldTV}, C#ctx.pid),
  {{lam, TV, FieldTV}, set_line(Line, C)};

infer({field, Expr, Var}, C) ->
  {ExprT, C1} = infer(Expr, C),
  Line = C1#ctx.line,
  {FieldT, C2} = infer({field, Var}, C1),

  TV = tv_server:fresh(C2#ctx.pid),
  From = ?FROM_FIELD_ACCESS(element(3, Var)),
  C3 = add_cst({lam, ExprT, TV}, FieldT, Line, From, C2),
  {TV, set_line(Line, C3)};

infer({app, Expr, Args}, C) ->
  {ExprT, C1} = infer(Expr, C),
  Line = C1#ctx.line,

  {ArgTsRev, C2} = lists:foldl(fun(Arg, {Ts, FoldC}) ->
    {T, FoldC1} = infer(Arg, FoldC),
    {[T | Ts], FoldC1}
  end, {[], C1}, Args),

  TV = tv_server:fresh(C2#ctx.pid),
  T = if
    length(ArgTsRev) == 0 -> {lam, none, TV};
    true ->
      lists:foldl(fun(ArgT, LastT) ->
        {lam, ArgT, LastT}
      end, TV, ArgTsRev)
  end,

  C3 = add_cst(T, ExprT, Line, ?FROM_APP, C2),
  {TV, set_line(Line, C3)};

infer({native, {atom, Line, Module}, {var, _, Name}, Arity}, C) ->
  % TODO: handle case where this fails
  ?LOG("Checking", {Module, Name, Arity}),
  true = erlang:function_exported(Module, list_to_atom(Name), Arity),
  T = if
    Arity == 0 -> {lam, none, tv_server:fresh(C#ctx.pid)};
    true ->
      lists:foldl(fun(_, LastT) ->
        {lam, tv_server:fresh(C#ctx.pid), LastT}
      end, tv_server:fresh(C#ctx.pid), lists:seq(1, Arity))
  end,

  {T, set_line(Line, C)};

infer({{'if', Line}, Expr, Then, Else}, C) ->
  {ExprT, C1} = infer(Expr, C),
  C2 = add_cst({con, 'Bool'}, ExprT, C1#ctx.line, ?FROM_IF_COND, C1),
  {ThenT, C3} = infer(Then, C2),

  case Else of
    {none, _} -> {none, set_line(Line, C3)};
    _ ->
      ThenLine = C3#ctx.line,
      {ElseT, C4} = infer(Else, C3),
      ElseLine = C4#ctx.line,

      TV = tv_server:fresh(C#ctx.pid),
      C5 = add_cst(TV, ThenT, ThenLine, ?FROM_IF_BODY, C4),
      C6 = add_cst(TV, ElseT, ElseLine, ?FROM_IF_BODY, C5),
      {TV, set_line(Line, C6)}
  end;

infer({{'let', Line}, Inits, Expr}, C) ->
  % TODO: ensure no pattern name overlap!
  {Gs, C1} = lists:mapfoldl(fun({Pattern, _}, FoldC) ->
    FoldC1 = with_pattern_env(Pattern, new_gnr(FoldC)),
    % save new gnr and revert it back to original
    {FoldC1#ctx.gnr, FoldC1#ctx{gnr=FoldC#ctx.gnr}}
  end, C, Inits),

  C2 = lists:foldl(fun({G, {Pattern, InitExpr}}, FoldC) ->
    {PatternT, FoldC1} = infer(Pattern, FoldC#ctx{gnr=G}),
    PatternLine = FoldC1#ctx.line,
    {InitExprT, FoldC2} = infer(InitExpr, FoldC1),

    FoldC3 = add_cst(PatternT, InitExprT, PatternLine, ?FROM_LET, FoldC2),
    finish_gnr(FoldC3, FoldC#ctx.gnr)
  end, C1, lists:zip(Gs, Inits)),

  {T, C3} = infer(Expr, C2),
  {T, set_line(Line, C3#ctx{env=C#ctx.env})};

infer({{if_let, Line}, {Pattern, Expr}, Then, Else}, C) ->
  C1 = with_pattern_env(Pattern, new_gnr(C)),
  {PatternT, C2} = infer(Pattern, C1),
  PatternLine = C2#ctx.line,

  {ExprT, C3} = infer(Expr, C2),
  C4 = add_cst(PatternT, ExprT, PatternLine, ?FROM_IF_LET_PATTERN, C3),
  {ThenT, C5} = infer(Then, finish_gnr(C4, C#ctx.gnr)),

  case Else of
    {none, _} -> {none, set_line(Line, C5)};
    _ ->
      ThenLine = C5#ctx.line,
      % must use original env without pattern bindings
      {ElseT, C6} = infer(Else, C5#ctx{env=C#ctx.env}),
      ElseLine = C6#ctx.line,

      TV = tv_server:fresh(C#ctx.pid),
      C7 = add_cst(TV, ThenT, ThenLine, ?FROM_IF_LET_BODY, C6),
      C8 = add_cst(TV, ElseT, ElseLine, ?FROM_IF_LET_BODY, C7),
      {TV, set_line(Line, C8)}
  end;

infer({{match, Line}, Expr, Cases}, C) ->
  TV = tv_server:fresh(C#ctx.pid),

  C1 = lists:foldl(fun({Pattern, Then}, FoldC) ->
    {ExprT, FoldC1} = infer(Expr, new_gnr(FoldC)),
    {PatternT, FoldC2} = infer(Pattern, with_pattern_env(Pattern, FoldC1)),
    PatternLine = FoldC2#ctx.line,
    FoldC3 = add_cst(ExprT, PatternT, PatternLine, ?FROM_MATCH_PATTERN, FoldC2),

    {ThenT, FoldC4} = infer(Then, finish_gnr(FoldC3, FoldC#ctx.gnr)),
    % revert env to before pattern was parsed
    FoldC5 = FoldC4#ctx{env=FoldC#ctx.env},
    add_cst(TV, ThenT, FoldC5#ctx.line, ?FROM_MATCH_BODY, FoldC5)
  end, C, Cases),

  {TV, set_line(Line, C1)};

infer({{block, Line}, Exprs}, C) ->
  {T, C1} = lists:foldl(fun(Expr, {_, FoldC}) ->
    infer(Expr, FoldC)
  end, {none, C}, Exprs),
  {T, set_line(Line, C1)};

infer({{Op, _}, Left, Right}, C) ->
  {LeftT, C1} = infer(Left, C),
  Line = C1#ctx.line,
  {RightT, C2} = infer(Right, C1),

  TV = tv_server:fresh(C2#ctx.pid),

  {T1, T2} = if
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

  C3 = add_cst(T1, T2, Line, ?FROM_OP(Op), C2),
  {TV, set_line(Line, C3)};

infer({{Op, Line}, Expr}, C) ->
  {ExprT, C1} = infer(Expr, C),
  TV = tv_server:fresh(C1#ctx.pid),

  {T1, T2} = if
    Op == '!' -> {{lam, ExprT, TV}, {lam, {con, 'Bool'}, {con, 'Bool'}}};
    Op == '#' ->
      ElemT = tv_server:fresh(C1#ctx.pid),
      {{lam, ExprT, TV}, {lam, {gen, 'List', ElemT}, {gen, 'Set', ElemT}}};
    Op == '-' ->
      NumT = tv_server:fresh('Num', C1#ctx.pid),
      {{lam, ExprT, TV}, {lam, NumT, NumT}};
    Op == 'discard' -> {TV, none}
  end,

  C2 = add_cst(T1, T2, Line, ?FROM_OP(Op), C1),
  {TV, set_line(Line, C2)}.

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
pattern_names({{list, _}, List}) -> pattern_names(List);
pattern_names({{list, _}, List, Rest}) ->
  gb_sets:union(pattern_names(List), pattern_names(Rest));
pattern_names({{tuple, _}, Left, Right}) ->
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

add_cst(T1, T2, Line, From, C) ->
  G = C#ctx.gnr,
  G1 = G#gnr{csts=[{T1, T2, Line, From} | G#gnr.csts]},
  C#ctx{gnr=G1}.

set_line(Line, C) -> C#ctx{line=Line}.

norm_sig_type(SigT, ExceptVs, Pid) ->
  ExceptVsSet = gb_sets:from_list(ExceptVs),

  % TODO: is it more intuitive to change each fv to *fv and then replace?
  Subs = gb_sets:fold(fun(V, FoldSubs) ->
    case gb_sets:is_member(V, ExceptVsSet) of
      true -> FoldSubs#{V => tv_server:next_name(Pid)};
      false -> FoldSubs#{V => {rigid, tv_server:next_name(Pid)}}
    end
  end, #{}, fvs(SigT)),

  subs(SigT, Subs).

param_type_to_list({tuple, LeftT, RightT}) ->
  [LeftT | param_type_to_list(RightT)];
param_type_to_list(T) -> [T].

lookup(Name, C) ->
  % TODO: handle case where can't find variable
  ?LOG("Looking up", Name),
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
        BoundVs = bound_vs(SolG#gnr.env, FoldS),

        lists:foldl(fun(SolV, NestedS) ->
          #solver{subs=Subs, schemes=Schemes} = NestedS,
          SolTV = {tv, SolV, none, false},
          T = subs(SolTV, Subs),
          GVs = gb_sets:subtract(fvs(T), BoundVs),
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
  BoundVs = bound_vs(Env, S),
  lists:foldl(fun({T1, T2, Line, From}, FoldS) ->
    FoldS1 = FoldS#solver{line=Line, from=From},
    unify(resolve(T1, FoldS), resolve(T2, FoldS), FoldS1)
  end, S#solver{bound_vs=BoundVs}, OrderedCsts).

resolve({lam, ArgT, ReturnT}, S) ->
  {lam, resolve(ArgT, S), resolve(ReturnT, S)};
resolve({tuple, LeftT, RightT}, S) ->
  {tuple, resolve(LeftT, S), resolve(RightT, S)};
resolve({tv, V, I, Rigid}, S) ->
  if
    is_map(I) ->
      NewI = maps:map(fun(_, T) -> resolve(T, S) end, I),
      {tv, V, NewI, Rigid};
    true -> {tv, V, I, Rigid}
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

unify(T1, T2, S) when T1 == T2 -> S;

unify({lam, ArgT1, ReturnT1}, {lam, ArgT2, ReturnT2}, S) ->
  S1 = unify(ArgT1, ArgT2, S),
  % TODO: should we short-circuit this unification if args failed?
  unify(ReturnT1, ReturnT2, S1);
unify({tuple, LeftT1, RightT1}, {tuple, LeftT2, RightT2}, S) ->
  S1 = unify(LeftT1, LeftT2, S),
  unify(RightT1, RightT2, S1);

unify({record, A1, FieldMap1}, {record, A2, FieldMap2}, S) ->
  Keys1 = gb_sets:from_list(maps:keys(FieldMap1)),
  Keys2 = gb_sets:from_list(maps:keys(FieldMap2)),

  if
    Keys1 /= Keys2 ->
      add_err({record, A1, FieldMap1}, {record, A2, FieldMap2}, S);

    true ->
      S1 = gb_sets:fold(fun(Key, FoldS) ->
        #{Key := T1} = FieldMap1,
        #{Key := T2} = FieldMap2,
        unify(T1, T2, FoldS)
      end, S, Keys1),

      if
        (A1 == none) or (A2 == none) -> S1;
        length(S#solver.errs) == length(S1#solver.errs) ->
          add_sub(A1, {record, A2, FieldMap2}, S1);
        true -> S1
      end
  end;

unify({tv, V1, I1, Rigid1}, {tv, V2, I2, Rigid2}, S) ->
  TV1 = {tv, V1, I1, Rigid1},
  TV2 = {tv, V2, I2, Rigid2},

  case {subs(TV1, S#solver.subs), subs(TV2, S#solver.subs)} of
    {TV1, TV2} ->
      Bound1 = gb_sets:is_member(V1, S#solver.bound_vs),
      Bound2 = gb_sets:is_member(V2, S#solver.bound_vs),
      Occurs = occurs(V1, TV2) or occurs(V2, TV1),

      if
        Occurs -> add_err(TV1, TV2, S);

        not Rigid1, not Bound1, Rigid2 ->
          case iface_lte(I1, I2, S) of
            false -> add_err(TV1, TV2, S);
            S1 -> add_sub(V1, TV2, S1)
          end;

        not Rigid2, not Bound2, Rigid1 ->
          case iface_lte(I2, I1, S) of
            false -> add_err(TV1, TV2, S);
            S1 -> add_sub(V2, TV1, S1)
         end;

        not Rigid1, not Rigid2 ->
          case iface_unify(I1, I2, S) of
            {I2, S1} -> add_sub(V1, TV2, S1);
            {I1, S1} -> add_sub(V2, TV1, S1);
            {NewI, S1} ->
              add_sub(V2, {set_iface, NewI}, add_sub(V1, TV2, S1));
            _ -> add_err(TV1, TV2, S)
          end;

        true -> add_err(TV1, TV2, S)
      end;

    {NewT1, NewT2} -> unify(NewT1, NewT2, S)
  end;
unify({tv, V, I, Rigid}, T, S) ->
  TV = {tv, V, I, Rigid},
  case {subs(TV, S#solver.subs), subs(T, S#solver.subs)} of
    {TV, T} ->
      Occurs = occurs(V, T),
      Instance = (I == none) or instance(T, I),
      Bound = gb_sets:is_member(V, S#solver.bound_vs),
      WouldEscape = Bound and occurs(true, T),

      if
        Occurs -> add_err(TV, T, S);
        Rigid or WouldEscape -> add_err(TV, T, S);

        Instance -> add_sub(V, T, S);
        is_map(I) ->
          case unalias(T, S) of
            {record, _, FieldMap} ->
              case iface_lte(I, FieldMap, S) of
                false -> add_err(TV, T, S);
                S1 -> add_sub(V, T, S1)
              end;
            T -> add_err(TV, T, S)
          end;

        true -> add_err(TV, T, S)
      end;

    {NewT1, NewT2} -> unify(NewT1, NewT2, S)
  end;
unify(T, {tv, V, I, Rigid}, S) -> unify({tv, V, I, Rigid}, T, S);

unify({gen, Con, ParamT1}, {gen, Con, ParamT2}, S) ->
  unify(ParamT1, ParamT2, S);

unify(T, {record, A, FieldMap}, S) ->
  RecordT = {record, A, FieldMap},
  case unalias(T, S) of
    T -> add_err(T, RecordT, S);
    NewT ->
      S1 = unify(NewT, RecordT, S),
      if
        length(S#solver.errs) == length(S1#solver.errs) -> add_sub(A, T, S1);
        true -> S1
      end
  end;
unify({record, A, FieldMap}, T, S) -> unify(T, {record, A, FieldMap}, S);

unify(T1, T2, S) ->
  case {unalias(T1, S), unalias(T2, S)} of
    {T1, _} -> add_err(T1, T2, S);
    {_, T2} -> add_err(T1, T2, S);
    {NewT1, NewT2} -> unify(NewT1, NewT2, S)
  end.

add_sub(V, Sub, S) ->
  S1 = case maps:find(V, S#solver.subs) of
    error -> S#solver{subs=(S#solver.subs)#{V => Sub}};
    % we're allowed to override set_iface to another value
    {ok, {set_iface, _}} -> S#solver{subs=(S#solver.subs)#{V => Sub}};
    {ok, Existing} -> error({badarg, V, Existing, Sub})
  end,

  BoundVs = S1#solver.bound_vs,
  case {Sub, gb_sets:is_member(V, BoundVs)} of
    % no change in fvs
    {{set_iface, _}, _} -> S1;
    % when subbing a tv not in env or an anchor
    {_, false} -> S1;
    {_, true} ->
      NewBoundVs = gb_sets:union(fvs(Sub), gb_sets:delete(V, BoundVs)),
      S1#solver{bound_vs=NewBoundVs}
  end.

add_err(T1, T2, S) ->
  #solver{subs=Subs, line=Line, from=From} = S,
  Err = {subs(T1, Subs), subs(T2, Subs), Line, From},
  S#solver{errs=[Err | S#solver.errs]}.

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
                unify(T1, T2, FoldS)
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
              {ok, T2} -> unify(T1, T2, FoldS);
              error -> FoldS
            end,
            {FoldMap#{Name => T1}, FoldS1}
          end, {#{}, S}, I1),

          {NewI, S2} = maps:fold(fun(Name, T2, {FoldMap, FoldS}) ->
            FoldS1 = case maps:find(Name, I1) of
              {ok, T1} -> unify(T1, T2, FoldS);
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
subs({tv, V, I, Rigid}, Subs) ->
  SubI = if
    is_map(I) -> element(3, subs({record, none, I}, Subs));
    true -> I
  end,

  case maps:find(V, Subs) of
    error -> {tv, V, SubI, Rigid};
    {ok, {rigid, V1}} -> {tv, V1, SubI, true};

    {ok, {set_iface, I1}} ->
      false = Rigid,
      if
        is_map(I1) ->
          SubI1 = element(3, subs({record, none, I1}, Subs)),
          {tv, V, SubI1, Rigid};
        true -> {tv, V, I1, Rigid}
      end;

    {ok, Value} ->
      Sub = if
        % Replacing with a new type entirely
        is_tuple(Value) or (Value == none) -> Value;
        % Instantiation, so rigid resets to false
        true -> {tv, Value, SubI, false}
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
    {ok, T} -> subs(T, Subs)
  end;
subs(none, _) -> none.

bound_vs(Env, S) ->
  #solver{subs=Subs, schemes=Schemes} = S,
  maps:fold(fun(_, Value, FoldVs) ->
    case Value of
      {no_dep, T} -> gb_sets:union(FoldVs, fvs(subs(T, Subs)));

      % 1) If a given other binding has been fully generalized already,
      %    we'll add the bound type variables from its scheme.
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
occurs(V, {tv, V1, I, Rigid}) ->
  OccursI = if
    is_map(I) -> occurs(V, {record, none, I});
    true -> false
  end,
  OccursI or (V == Rigid) or (V == V1);
occurs(_, {con, _}) -> false;
occurs(V, {gen, _, ParamT}) -> occurs(V, ParamT);
% occurs({inst, ...}) ommitted; they should be resolved
occurs(V, {record, _, FieldMap}) ->
  maps:fold(fun(_, T, Occurs) ->
    Occurs or occurs(V, T)
  end, false, FieldMap);
occurs(_, none) -> false.

pretty_csts([]) -> [];
pretty_csts([{T1, T2, Line, From} | Rest]) ->
  [{pretty(T1), pretty(T2), Line, From} | pretty_csts(Rest)].

pretty({lam, ArgT, ReturnT}) ->
  Format = case ArgT of
    {lam, _, _} -> "(~s) -> ~s";
    _ -> "~s -> ~s"
  end,
  ?FMT(Format, [pretty(ArgT), pretty(ReturnT)]);
pretty({tuple, LeftT, RightT}) ->
  ?FMT("(~s, ~s)", [pretty(LeftT), pretty_strip_parens(RightT)]);
pretty({tv, V, I, Rigid}) ->
  Str = if
    I == none -> tl(V);
    is_map(I) -> ?FMT("{ ~s | ~s }", [tl(V), pretty_field_map(I)]);
    true -> ?FMT("~s: ~s", [tl(V), atom_to_list(I)])
  end,

  case Rigid of
    false -> Str;
    true -> ?FMT("rigid(~s)", [Str])
  end;
pretty({set_iface, I}) ->
  Str = if
    is_map(I) -> pretty_field_map(I);
    true -> atom_to_list(I)
  end,
  ?FMT("I = ~s", [Str]);
pretty({con, Con}) -> atom_to_list(Con);
pretty({gen, 'List', ParamT}) ->
  ?FMT("[~s]", [pretty_strip_parens(ParamT)]);
pretty({gen, T, ParamT}) ->
  ?FMT("~s<~s>", [atom_to_list(T), pretty_strip_parens(ParamT)]);
pretty({inst, TV}) ->
  ?FMT("inst(~s)", [pretty(TV)]);
pretty({record, _, FieldMap}) ->
  ?FMT("{ ~s }", [pretty_field_map(FieldMap)]);
pretty(none) -> "()".

pretty_strip_parens({tuple, LeftT, RightT}) ->
  ?FMT("~s, ~s", [pretty(LeftT), pretty_strip_parens(RightT)]);
pretty_strip_parens(T) -> pretty(T).

pretty_field_map(FieldMap) ->
  FieldStrs = maps:fold(fun(Name, T, Strs) ->
    [?FMT("~s :: ~s", [Name, pretty(T)]) | Strs]
  end, [], FieldMap),
  string:join(lists:sort(FieldStrs), ", ").
