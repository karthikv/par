-module(type_system).
-export([
  infer_file/1,
  infer_prg/1,
  pretty/1,
  pattern_names/1
]).
-on_load(load/0).
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
%   {tuple, Ts} - a tuple type (T1, T2, ...); e.g. (Int, Bool)
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
%   types - a Name => Int (number of type params) map for types in the env
%   structs - a Name => StructInfo map for structs in the env
%   ifaces - a map of V => I for TV names in a signature to ensure consistency
%   errs - an array of error messages, each of the form {Msg, Loc}
%   pid - the process id of the TV server used to generated fresh TVs
-record(ctx, {
  gnr = undefined,
  gnrs = [],
  env = #{},
  types = #{
    "Int" => 0,
    "Float" => 0,
    "Bool" => 0,
    "Atom" => 0,
    "Char" => 0,
    "String" => 0,
    "List" => 1,
    "Set" => 1,
    "Map" => 2
  },
  structs = #{},
  ifaces = #{},
  errs = [],
  modules = gb_sets:new(),
  module,
  pid
}).

% S - a solver record used to unify types and solve constraints
%   subs - the substitutions made to unify types
%   errs - any constraints that couldn't be unified
%   schemes - the schemes of env variables that have been solved for and
%             generalized
%   bound_vs - the set of TV names in the environment
%   structs - a Name => StructInfo map for structs in the env
%   module - the module of the current constraint that's being unified
%   loc - the location of the current constraint that's being unified
%   from - a string describing where the current constraint is from
%   pid - the process id of the TV server used to generated fresh TVs
-record(solver, {
  subs = #{},
  errs = [],
  schemes = #{},
  bound_vs,
  structs = #{},
  t1,
  t2,
  module,
  loc,
  from,
  pid
}).

% G - a gnr record that represents a set of constraints to solve before
%     generalizing a type variable:
%   v - the TV name to generalize
%   env - see Env above
%   csts - an array of constraints to solve before generalizing
%   deps - a set of TV names corresponding to gnr records that need to solved
%          before this record or, in the case of (mutual) recursion,
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

-ifdef(TEST).
  -define(
    LOG(Prefix, Value),
    io:format("~n(~p:~p) ~s:~n~p~n", [?MODULE, ?LINE, Prefix, Value])
  ).
-else.
  -define(LOG(Prefix, Value), true).
-endif.

% this also initializes the lexer by dependency
load() -> 'Parser':'_@init'(gb_sets:new()).

infer_file(Path) ->
  {_, Comps, _} = parse_file(Path, #{}),
  infer_comps(Comps).

parse_file(RawPath, Parsed) ->
  Path = case filename:extension(RawPath) of
    "" -> utils:absolute(RawPath ++ ".par");
    _ -> utils:absolute(RawPath)
  end,

  case maps:find(Path, Parsed) of
    {ok, Module} -> {Module, [], Parsed};
    error ->
      {ok, Binary} = file:read_file(Path),
      Contents = binary_to_list(Binary),
      {ok, Tokens} = 'Lexer':tokenize(Contents),

      #{value := {some, Ast}, errs := []} = 'Parser':parse(Tokens),
      {module, _, {con_token, _, Module}, Imports, _} = Ast,
      Parsed1 = Parsed#{Path => Module},

      Dir = filename:dirname(Path),
      {Deps, Comps, Parsed2} = lists:foldr(fun(Import, Memo) ->
        {import, _, {str, _, DepPath}} = Import,
        {FoldModules, FoldComps, FoldParsed} = Memo,

        FullPath = filename:join(Dir, binary_to_list(DepPath)),
        {DepModule, DepComps, FoldParsed1} = parse_file(FullPath, FoldParsed),
        {[DepModule | FoldModules], [DepComps | FoldComps], FoldParsed1}
      end, {[], [], Parsed1}, Imports),

      Comp = #comp{
        module=Module,
        ast=Ast,
        deps=Deps,
        path=Path,
        contents=Contents
      },
      {Module, lists:append([[Comp] | Comps]), Parsed2}
  end.

infer_prg(Prg) ->
  {ok, Tokens} = if
    is_list(Prg) -> 'Lexer':tokenize(Prg);
    is_binary(Prg) -> 'Lexer':tokenize(Prg)
  end,

  #{value := {some, Ast}, errs := []} = 'Parser':parse(Tokens),
  % infer_prg should only be used only when there are no imports
  {module, _, {con_token, _, Module}, [], _} = Ast,
  %% ?LOG("Ast", Ast),

  Comp = #comp{
    module=Module,
    ast=Ast,
    deps=[],
    path="[infer-prg]",
    contents=Prg
  },
  infer_comps([Comp]).

infer_comps(Comps) ->
  {ok, Pid} = tv_server:start_link(),

  {_, C} = lists:foldl(fun(Comp, {Modules, FoldC}) ->
    #comp{module=Module, ast={module, _, {con_token, Loc, _}, _, _}} = Comp,
    FoldC1 = FoldC#ctx{module=Module},

    case gb_sets:is_member(Module, Modules) of
      true -> {Modules, add_ctx_err(?ERR_REDEF_MODULE(Module), Loc, FoldC1)};
      false -> {gb_sets:add(Module, Modules), FoldC1}
    end
  end, {gb_sets:new(), #ctx{pid=Pid}}, Comps),

  C1 = lists:foldl(fun(Comp, FoldC) ->
    #comp{module=Module, ast={module, _, _, _, Defs}} = Comp,

    lists:foldl(fun(Node, ModuleC) ->
      case Node of
        {global, _, {var, Loc, Name}, _, Exported} ->
          case env_exists(Name, ModuleC) of
            true -> add_ctx_err(?ERR_REDEF(Name), Loc, ModuleC);
            false ->
              {TV, ID} = tv_server:fresh_gnr_id(ModuleC#ctx.pid),
              env_add(Name, {add_dep, TV, ID}, Exported, ModuleC)
          end;

        {N, _, TE, _} when N == enum; N == struct ->
          {Loc, RawCon, NumParams} = case TE of
            {con_token, Loc_, RawCon_} -> {Loc_, RawCon_, 0};
            {gen_te, _, {con_token, Loc_, RawCon_}, ParamTEs} ->
              {Loc_, RawCon_, length(ParamTEs)}
          end,

          Con = qualify(RawCon, ModuleC),
          Types = ModuleC#ctx.types,

          RedefBuiltin = (string:chr(RawCon, $.) == 0) and
            maps:is_key(RawCon, Types),
          Redef = maps:is_key(Con, Types),

          if
            RedefBuiltin ->
              add_ctx_err(?ERR_REDEF_BUILTIN_TYPE(RawCon), Loc, ModuleC);

            % TODO: add line numbers for where redef occurred
            Redef -> add_ctx_err(?ERR_REDEF_TYPE(Con), Loc, ModuleC);
            true -> ModuleC#ctx{types=Types#{Con => NumParams}}
          end;

        _ -> ModuleC
      end
    end, FoldC#ctx{module=Module}, Defs)
  end, C, Comps),

  C2 = lists:foldl(fun(Comp, FoldC) ->
    #comp{module=Module, ast={module, _, _, _, Defs}, deps=Deps} = Comp,
    AccessibleModules = gb_sets:from_list([Module | Deps]),
    FoldC1 = FoldC#ctx{module=Module, modules=AccessibleModules},

    lists:foldl(fun(Node, ModuleC) ->
      case Node of
        {N, _, _, _} when N == enum; N == struct ->
          {_, ModuleC1} = infer(Node, ModuleC),
          ModuleC1;

        _ -> ModuleC
      end
    end, FoldC1, Defs)
  end, C1, Comps),

  C3 = lists:foldl(fun(Comp, FoldC) ->
    #comp{module=Module, ast={module, _, _, _, Defs}, deps=Deps} = Comp,
    AccessibleModules = gb_sets:from_list([Module | Deps]),
    FoldC1 = FoldC#ctx{module=Module, modules=AccessibleModules},

    {LastSig, FoldC2} = lists:foldl(fun(Node, {Sig, ModuleC}) ->
      ModuleC1 = if
        Sig == none -> ModuleC;
        true ->
          {sig, _, {var, _, SigName}, _} = Sig,
          case Node of
            {global, _, {var, _, SigName}, _, _} -> ModuleC;
            _ -> add_ctx_err(?ERR_SIG_NO_DEF(SigName), ?LOC(Sig), ModuleC)
          end
      end,

      case Node of
        {global, Loc, {var, _, Name}, Expr, _} ->
          {add_dep, TV, ID} = env_get(Name, ModuleC1),
          ModuleC2 = case Expr of
            {fn, _, _, _} -> ModuleC1;
            _ -> env_remove(Name, ModuleC1)
          end,

          ModuleC3 = new_gnr(TV, ID, ModuleC2),
          {T, ModuleC4} = infer(Expr, ModuleC3),
          ExprCst = make_cst(TV, T, Loc, ?FROM_GLOBAL_DEF(Name), ModuleC4),

          {InitCsts, ModuleC6} = if
            Sig == none -> {[ExprCst], ModuleC4};
            true ->
              {SigT, ModuleC5} = infer(Sig, ModuleC4),
              SigCst = make_cst(
                TV,
                SigT,
                ?LOC(Sig),
                ?FROM_GLOBAL_SIG(Name),
                ModuleC5
              ),
              {[SigCst, ExprCst], ModuleC5}
          end,

          ModuleC7 = ModuleC6#ctx{env=ModuleC#ctx.env},
          ModuleC8 = finish_gnr(ModuleC7, ModuleC#ctx.gnr),

          % Unifying the expr and sig constraints first generally gives better
          % error messages. To do this, we create a new gnr containing just
          % these constraints, and make all other gnrs for this global depend
          % on it.
          ModuleC9 = new_gnr(ModuleC8),
          ModuleC10 = ModuleC9#ctx{gnr=ModuleC9#ctx.gnr#gnr{csts=InitCsts}},

          DepID = ModuleC10#ctx.gnr#gnr.id,
          UntilID = case ModuleC2#ctx.gnrs of
            [G | _] -> G#gnr.id;
            [] -> none
          end,

          {Gs, _} = lists:mapfoldl(fun(G, Done) ->
            case Done of
              true -> {G, Done};
              false -> {add_gnr_dep(DepID, G), G#gnr.id == UntilID}
            end
          end, false, ModuleC10#ctx.gnrs),
          {none, finish_gnr(ModuleC10#ctx{gnrs=Gs}, ModuleC#ctx.gnr)};

        {sig, _, _, _} -> {Node, ModuleC1};

        % we've already processed enums/structs
        _ -> {none, ModuleC1}
      end
    end, {none, FoldC1}, Defs),

    case LastSig of
      none -> FoldC2;
      {sig, _, {var, _, SigName}, _} ->
        add_ctx_err(?ERR_SIG_NO_DEF(SigName), ?LOC(LastSig), FoldC2)
    end
  end, C2, Comps),

  S = #solver{errs=C3#ctx.errs, structs=C3#ctx.structs, pid=Pid},
  Result = case solve(C3#ctx.gnrs, S) of
    {ok, Schemes} ->
      SubbedEnv = maps:map(fun(_, {Value, Exported}) ->
        {tv, V, _, _} = case Value of
          {no_dep, TV} -> TV;
          {add_dep, TV, _} -> TV
        end,
        {inst(maps:get(V, Schemes), Pid), Exported}
      end, C3#ctx.env),
      {ok, SubbedEnv, Comps};

    {errors, Errs} -> {errors, Errs, Comps}
  end,

  % TODO: how to require that main is defined?
  ok = tv_server:stop(Pid),
  Result.

infer({fn, _, Args, Expr}, C) ->
  {ArgTsRev, C1} = lists:foldl(fun({var, _, ArgName}, {Ts, FoldC}) ->
    ArgTV = tv_server:fresh(FoldC#ctx.pid),
    {[ArgTV | Ts], env_add(ArgName, {no_dep, ArgTV}, false, FoldC)}
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

infer({sig, _, _, Sig}, C) ->
  {SigT, C1} = infer_sig(false, false, #{}, Sig, C),
  {norm_sig_type(SigT, maps:keys(C1#ctx.ifaces), C#ctx.pid), C1};

infer({binary_op, Loc, '::', Expr, Sig}, C) ->
  G = C#ctx.gnr,
  {TV, ID} = tv_server:fresh_gnr_id(C#ctx.pid),

  {ExprT, C1} = infer(Expr, new_gnr(TV, ID, C)),
  {SigT, C2} = infer_sig(false, false, #{}, Sig, C1),
  NormSigT = norm_sig_type(SigT, maps:keys(C2#ctx.ifaces), C2#ctx.pid),

  C3 = add_cst(TV, ExprT, ?LOC(Expr), ?FROM_EXPR_SIG, C2),
  C4 = add_cst(TV, NormSigT, Loc, ?FROM_EXPR_SIG, C3),
  C5 = finish_gnr(C4, add_gnr_dep(ID, G)),

  {{inst, TV}, C5};

infer({enum, _, EnumTE, Options}, C) ->
  {T, C1} = infer_sig(false, true, #{}, EnumTE, C),
  FVs = fvs(T),

  {_, C2} = lists:foldl(fun(Option, {Keys, FoldC}) ->
    {{con_token, Loc, Con}, ArgTEs, KeyNode} = Option,
    {ArgTsRev, FoldC1} = lists:foldl(fun(ArgTE, {Ts, NestedC}) ->
      {ArgT, NestedC1} = infer_sig(
        {T, FVs},
        false,
        NestedC#ctx.ifaces,
        ArgTE,
        NestedC
      ),
      {[ArgT | Ts], NestedC1}
    end, {[], FoldC}, ArgTEs),

    OptionT = lists:foldl(fun(ArgT, LastT) ->
      {lam, ArgT, LastT}
    end, T, ArgTsRev),

    % don't need to make any Vs rigid; inst still works correctly
    NormOptionT = norm_sig_type(OptionT, [], C#ctx.pid),

    {TV, ID} = tv_server:fresh_gnr_id(C#ctx.pid),
    FoldC2 = new_gnr(TV, ID, FoldC1),
    FoldC3 = add_cst(TV, NormOptionT, Loc, ?FROM_ENUM_CTOR, FoldC2),
    FoldC4 = finish_gnr(FoldC3, FoldC1#ctx.gnr),

    Name = utils:unqualify(Con),
    FoldC5 = case env_exists(Name, FoldC4) of
      true -> add_ctx_err(?ERR_REDEF(Name), Loc, FoldC4);
      false -> env_add(Name, {add_dep, TV, ID}, true, FoldC4)
    end,

    case KeyNode of
      none ->
        Key = list_to_atom(Con),
        case maps:find(Key, Keys) of
          {ok, {default, _, _}} ->
            % we've already added an ERR_REDEF; no need to add another
            {Keys, FoldC5};
          {ok, {custom, _, CustomLoc}} ->
            % TODO: show actual code instead of just line for ERR_DUP_KEY
            FoldC6 = add_ctx_err(
              ?ERR_DUP_KEY(Key, Con, Loc),
              CustomLoc,
              FoldC5
            ),
            {Keys, FoldC6};
          error -> {Keys#{Key => {default, Con, Loc}}, FoldC5}
        end;

      {some, {atom, KeyLoc, Key}} ->
        case maps:find(Key, Keys) of
          {ok, {_, OtherCon, OtherLoc}} ->
            FoldC6 = add_ctx_err(
              ?ERR_DUP_KEY(Key, OtherCon, OtherLoc),
              KeyLoc,
              FoldC5
            ),

            % In case the map contains a default, we go ahead and replace the
            % value with a custom. This way, if another default comes up, we'll
            % correctly report an error.
            {Keys#{Key := {custom, Con, KeyLoc}}, FoldC6};
          error -> {Keys#{Key => {custom, Con, KeyLoc}}, FoldC5}
        end
    end
  end, {#{}, C1}, Options),

  {T, C2};

infer({struct, Loc, StructTE, Fields}, C) ->
  {T, C1} = infer_sig(false, true, #{}, StructTE, C),
  {{record, _, RawFieldMap}, C2} = infer_sig(
    {T, fvs(T)},
    false,
    C1#ctx.ifaces,
    {record_te, Loc, Fields},
    C1
  ),

  FnT = lists:foldr(fun({{var, _, Name}, _}, LastT) ->
    #{Name := FieldT} = RawFieldMap,
    {lam, FieldT, LastT}
  end, T, Fields),

  % don't need to make any Vs rigid; inst still works correctly
  NormFnT = norm_sig_type(FnT, [], C2#ctx.pid),

  {Con, ConLoc, Value} = case {T, StructTE} of
    {{con, Con_}, {con_token, ConLoc_, _}} ->
      {Con_, ConLoc_, {T, [], RawFieldMap}};

    {{gen, Con_, ParamTs}, {gen_te, _, {con_token, ConLoc_, _}, _}} ->
      Vs = lists:map(fun({tv, V, none, _}) -> V end, ParamTs),
      {Con_, ConLoc_, {T, Vs, RawFieldMap}}
  end,

  {TV, ID} = tv_server:fresh_gnr_id(C2#ctx.pid),
  Name = utils:unqualify(Con),
  C3 = case env_exists(Name, C2) of
    true -> add_ctx_err(?ERR_REDEF(Name), ConLoc, C2);
    false ->
      NewStructs = (C2#ctx.structs)#{Con => Value},
      env_add(Name, {add_dep, TV, ID}, true, C2#ctx{structs=NewStructs})
  end,

  C4 = new_gnr(TV, ID, C3),
  C5 = add_cst(TV, NormFnT, Loc, ?FROM_STRUCT_CTOR, C4),
  C6 = finish_gnr(C5, C3#ctx.gnr),

  {TV, C6};

infer({none, _}, C) -> {none, C};
infer({int, _, _}, C) ->
  {tv_server:fresh("Num", C#ctx.pid), C};
infer({float, _, _}, C) -> {{con, "Float"}, C};
infer({bool, _, _}, C) -> {{con, "Bool"}, C};
infer({char, _, _}, C) -> {{con, "Char"}, C};
infer({str, _, _}, C) -> {{con, "String"}, C};
infer({atom, _, _}, C) -> {{con, "Atom"}, C};

infer({list, _, Elems}, C) ->
  TV = tv_server:fresh(C#ctx.pid),

  C1 = lists:foldl(fun(Elem, FoldC) ->
    {ElemT, FoldC1} = infer(Elem, FoldC),
    add_cst(ElemT, TV, ?LOC(Elem), ?FROM_LIST_ELEM, FoldC1)
  end, C, Elems),

  {{gen, "List", [TV]}, C1};

infer({cons, Loc, Elems, Tail}, C) ->
  {T, C1} = infer({list, Loc, Elems}, C),
  {TailT, C2} = infer(Tail, C1),
  C3 = add_cst(T, TailT, ?LOC(Tail), ?FROM_LIST_TAIL, C2),
  {T, C3};

infer({tuple, _, Elems}, C) ->
  {ElemTs, C1} = lists:mapfoldl(fun(Elem, FoldC) ->
    infer(Elem, FoldC)
  end, C, Elems),
  {{tuple, ElemTs}, C1};

infer({map, _, Pairs}, C) ->
  KeyTV = tv_server:fresh(C#ctx.pid),
  ValueTV = tv_server:fresh(C#ctx.pid),

  C1 = lists:foldl(fun({Key, Value}, FoldC) ->
    {KeyT, FoldC1} = infer(Key, FoldC),
    FoldC2 = add_cst(KeyT, KeyTV, ?LOC(Key), ?FROM_MAP_KEY, FoldC1),
    {ValueT, FoldC3} = infer(Value, FoldC2),
    add_cst(ValueT, ValueTV, ?LOC(Value), ?FROM_MAP_VALUE, FoldC3)
  end, C, Pairs),

  {{gen, "Map", [KeyTV, ValueTV]}, C1};

infer({N, Loc, Name}, C) when N == var; N == con_token; N == var_value ->
  lookup(C#ctx.module, Name, Loc, C);

% only occurs when pattern matching to designate anything
infer({'_', _}, C) -> {tv_server:fresh(C#ctx.pid), C};

infer({anon_record, _, Inits}, C) ->
  {FieldMap, C1} = lists:foldl(fun(Init, {Map, FoldC}) ->
    {{var, Loc, Name}, Expr} = Init,
    {T, FoldC1} = infer(Expr, FoldC),

    case maps:is_key(Name, Map) of
      true -> {Map, add_ctx_err(?ERR_DUP_FIELD(Name), Loc, FoldC1)};
      false -> {Map#{Name => T}, FoldC1}
    end
  end, {#{}, C}, Inits),

  {{record, tv_server:next_name(C1#ctx.pid), FieldMap}, C1};

infer({anon_record_ext, Loc, Expr, AllInits}, C) ->
  {ExprT, C1} = infer(Expr, C),
  {Inits, ExtInits} = lists:foldl(fun({Init, IsExt}, Memo) ->
    {FoldInits, FoldExtInits} = Memo,
    case IsExt of
      true -> {FoldInits, [Init | FoldExtInits]};
      false -> {[Init | FoldInits], FoldExtInits}
    end
  end, {[], []}, AllInits),

  C3 = if
    length(Inits) == 0 -> C1;
    true ->
      {{record, A, FieldMap}, C2} = infer({anon_record, Loc, Inits}, C1),
      add_cst(
        ExprT,
        {record_ext, A, tv_server:fresh(C2#ctx.pid), FieldMap},
        Loc,
        ?FROM_RECORD_UPDATE,
        C2
      )
  end,

  if
    length(ExtInits) == 0 -> {ExprT, C3};
    true ->
      {{record, ExtA, Ext}, C4} = infer({anon_record, Loc, ExtInits}, C3),
      % ExprT needs to have every field in ext, but the types can be different
      % because it's a record extension.
      RelaxedExt = maps:map(fun(_, _) -> tv_server:fresh(C4#ctx.pid) end, Ext),

      C5 = add_cst(
        ExprT,
        {record_ext, ExtA, tv_server:fresh(C4#ctx.pid), RelaxedExt},
        Loc,
        ?FROM_RECORD_UPDATE,
        C4
      ),

      {{record_ext, tv_server:next_name(C5#ctx.pid), ExprT, Ext}, C5}
  end;

infer({record, Loc, {con_token, ConLoc, Name}, Inits}, C) ->
  Con = qualify(Name, C),
  case maps:find(Con, C#ctx.structs) of
    {ok, {StructT, _, _}} ->
      {RecordT, C1} = infer({anon_record, Loc, Inits}, C),
      NormSigT = norm_sig_type(StructT, [], C1#ctx.pid),
      From = ?FROM_RECORD_CREATE(Name),

      TV = tv_server:fresh(C1#ctx.pid),
      C2 = add_cst(TV, RecordT, Loc, From, C1),
      C3 = add_cst(TV, NormSigT, Loc, From, C2),
      {TV, C3};

    error ->
      {RecordT, C1} = infer({anon_record, Loc, Inits}, C),
      {RecordT, add_ctx_err(?ERR_NOT_DEF_TYPE(Name), ConLoc, C1)}
  end;

infer({record_ext, Loc, {con_token, ConLoc, Name}, Expr, AllInits}, C) ->
  Con = qualify(Name, C),
  case maps:find(Con, C#ctx.structs) of
    {ok, {StructT, _, _}} ->
      {RecordT, C1} = infer({anon_record_ext, Loc, Expr, AllInits}, C),
      NormSigT = norm_sig_type(StructT, [], C1#ctx.pid),
      From = ?FROM_RECORD_UPDATE,

      TV = tv_server:fresh(C1#ctx.pid),
      C2 = add_cst(TV, RecordT, Loc, From, C1),
      C3 = add_cst(TV, NormSigT, Loc, From, C2),
      {TV, C3};

    error ->
      {RecordT, C1} = infer({anon_record_ext, Loc, Expr, AllInits}, C),
      {RecordT, add_ctx_err(?ERR_NOT_DEF_TYPE(Name), ConLoc, C1)}
  end;

infer({field_fn, _, {var, _, Name}}, C) ->
  FieldTV = tv_server:fresh(C#ctx.pid),
  BaseTV = tv_server:fresh(C#ctx.pid),
  A = tv_server:next_name(C#ctx.pid),
  RecordExtT = {record_ext, A, BaseTV, #{Name => FieldTV}},
  {{lam, RecordExtT, FieldTV}, C};

% TODO: ensure this is parsed correctly or add error cases (e.g. when var is
% a con_token, expr must be a con_token)
infer({field, Loc, Expr, {N, _, Name}=Var}, C)
    when N == var; N == con_token ->
  case Expr of
    {con_token, ConLoc, Module} ->
      case gb_sets:is_member(Module, C#ctx.modules) of
        true -> lookup(Module, Name, Loc, C);
        false ->
          TV = tv_server:fresh(C#ctx.pid),
          {TV, add_ctx_err(?ERR_NOT_DEF_MODULE(Module), ConLoc, C)}
      end;

    _ ->
      {ExprT, C1} = infer(Expr, C),
      {{lam, RecordExtT, ResultT}, C2} = infer({field_fn, ?LOC(Var), Var}, C1),
      From = ?FROM_FIELD_ACCESS(element(3, Var)),
      C3 = add_cst(ExprT, RecordExtT, Loc, From, C2),
      {ResultT, C3}
  end;

infer({app, Loc, Expr, Args}, C) ->
  {ExprT, C1} = infer(Expr, C),
  {ArgLocTsRev, C2} = lists:foldl(fun(Arg, {LocTs, FoldC}) ->
    {T, FoldC1} = infer(Arg, FoldC),
    {[{?LOC(Arg), T} | LocTs], FoldC1}
  end, {[], C1}, Args),

  TV = tv_server:fresh(C2#ctx.pid),
  T = if
    length(ArgLocTsRev) == 0 -> {lam, none, TV};
    true ->
      lists:foldl(fun({ArgLoc, ArgT}, LastT) ->
        {lam, ArgLoc, ArgT, LastT}
      end, TV, ArgLocTsRev)
  end,

  C3 = add_cst(T, ExprT, Loc, ?FROM_APP, C2),
  {TV, C3};

infer({native, Loc, {atom, _, Module}, {var, _, Name}, Arity}, C) ->
  C1 = case erlang:function_exported(Module, list_to_atom(Name), Arity) of
    true -> C;
    false -> add_ctx_err(?ERR_NOT_DEF_NATIVE(Module, Name, Arity), Loc, C)
  end,

  T = if
    Arity == 0 -> {lam, none, tv_server:fresh(C1#ctx.pid)};
    true ->
      lists:foldl(fun(_, LastT) ->
        {lam, tv_server:fresh(C1#ctx.pid), LastT}
      end, tv_server:fresh(C1#ctx.pid), lists:seq(1, Arity))
  end,

  {T, C1};

infer({'if', _, Expr, Then, Else}, C) ->
  {ExprT, C1} = infer(Expr, C),
  C2 = add_cst({con, "Bool"}, ExprT, ?LOC(Expr), ?FROM_IF_COND, C1),
  {ThenT, C3} = infer(Then, C2),

  case Else of
    {none, _} -> {none, C3};
    _ ->
      {ElseT, C4} = infer(Else, C3),
      TV = tv_server:fresh(C#ctx.pid),
      C5 = add_cst(TV, ThenT, ?LOC(Then), ?FROM_THEN_BODY, C4),
      C6 = add_cst(TV, ElseT, ?LOC(Else), ?FROM_ELSE_BODY, C5),
      {TV, C6}
  end;

infer({'let', _, Inits, Then}, C) ->
  C1 = lists:foldl(fun({Pattern, Expr}, FoldC) ->
    infer_pattern(Pattern, Expr, ?FROM_LET, FoldC)
  end, C, Inits),

  {T, C2} = infer(Then, C1),
  {T, C2#ctx{env=C#ctx.env}};

infer({if_let, _, {Pattern, Expr}, Then, Else}, C) ->
  C1 = infer_pattern(Pattern, Expr, ?FROM_IF_LET_PATTERN, C),
  {ThenT, C2} = infer(Then, C1),
  % revert env to before pattern was parsed
  C3 = C2#ctx{env=C#ctx.env},

  case Else of
    {none, _} -> {none, C3};
    _ ->
      % must use original env without pattern bindings
      {ElseT, C4} = infer(Else, C3),
      TV = tv_server:fresh(C4#ctx.pid),
      C5 = add_cst(TV, ThenT, ?LOC(Then), ?FROM_THEN_BODY, C4),
      C6 = add_cst(TV, ElseT, ?LOC(Else), ?FROM_ELSE_BODY, C5),
      {TV, C6}
  end;

infer({match, _, Expr, Cases}, C) ->
  TV = tv_server:fresh(C#ctx.pid),

  C1 = lists:foldl(fun({Pattern, Then}, FoldC) ->
    {ExprT, FoldC1} = infer(Expr, new_gnr(FoldC)),
    {PatternT, FoldC2} = infer(Pattern, with_pattern_env(Pattern, FoldC1)),
    FoldC3 = add_cst(
      ExprT,
      PatternT,
      ?LOC(Pattern),
      ?FROM_MATCH_PATTERN,
      FoldC2
    ),

    {ThenT, FoldC4} = infer(Then, finish_gnr(FoldC3, FoldC#ctx.gnr)),
    % revert env to before pattern was parsed
    FoldC5 = FoldC4#ctx{env=FoldC#ctx.env},
    add_cst(TV, ThenT, ?LOC(Then), ?FROM_MATCH_BODY, FoldC5)
  end, C, Cases),

  {TV, C1};

infer({block, _, Exprs}, C) ->
  {T, C1} = lists:foldl(fun(Expr, {_, FoldC}) ->
    infer(Expr, FoldC)
  end, {none, C}, Exprs),
  {T, C1};

infer({binary_op, _, '|>', Left, Right}, C) ->
  {LeftT, C1} = infer(Left, C),
  {RightT, C2} = infer(Right, C1),

  TV = tv_server:fresh(C2#ctx.pid),
  ArgTV = tv_server:fresh(C2#ctx.pid),

  % The left constraint will always unify successfully if processed first. To
  % get better error messages, add the right constraint first, so it's possible
  % for the left constraint to fail. This is the main reason |> is in a separate
  % function clause than the rest of the binary operators below.
  C3 = add_cst({lam, ArgTV, TV}, RightT, ?LOC(Right), ?FROM_OP_RHS('|>'), C2),
  C4 = add_cst(ArgTV, LeftT, ?LOC(Left), ?FROM_OP_LHS('|>'), C3),
  {TV, C4};

infer({binary_op, Loc, Op, Left, Right}, C) ->
  {LeftT, C1} = infer(Left, C),
  {RightT, C2} = infer(Right, C1),
  TV = tv_server:fresh(C2#ctx.pid),

  {ExpLeftT, ExpRightT, ResultT} = if
    Op == '=='; Op == '!=' ->
      OperandTV = tv_server:fresh(C2#ctx.pid),
      {OperandTV, OperandTV, {con, "Bool"}};
    Op == '||'; Op == '&&' ->
      {{con, "Bool"}, {con, "Bool"}, {con, "Bool"}};
    Op == '>'; Op == '<'; Op == '>='; Op == '<=' ->
      NumTV = tv_server:fresh("Num", C2#ctx.pid),
      {NumTV, NumTV, {con, "Bool"}};
    Op == '+'; Op == '-'; Op == '*'; Op == '/' ->
      NumTV = tv_server:fresh("Num", C2#ctx.pid),
      ReturnT = if Op == '/' -> {con, "Float"}; true -> NumTV end,
      {NumTV, NumTV, ReturnT};
    Op == '%' ->
      ReturnTV = tv_server:fresh("Num", C2#ctx.pid),
      {{con, "Int"}, {con, "Int"}, ReturnTV};
    Op == '++' ->
      OperandTV = tv_server:fresh("Concatable", C2#ctx.pid),
      {OperandTV, OperandTV, OperandTV};
    Op == '--' ->
      OperandTV = tv_server:fresh("Separable", C2#ctx.pid),
      {OperandTV, OperandTV, OperandTV}
  end,

  C3 = add_cst(ExpLeftT, LeftT, ?LOC(Left), ?FROM_OP_LHS(Op), C2),
  C4 = add_cst(ExpRightT, RightT, ?LOC(Right), ?FROM_OP_RHS(Op), C3),
  C5 = add_cst(ResultT, TV, Loc, ?FROM_OP_RESULT(Op), C4),
  {TV, C5};

infer({unary_op, Loc, Op, Expr}, C) ->
  {ExprT, C1} = infer(Expr, C),
  TV = tv_server:fresh(C1#ctx.pid),

  {ExpExprT, ResultT} = if
    Op == '!' -> {{con, "Bool"}, {con, "Bool"}};
    Op == '#' ->
      ElemT = tv_server:fresh(C1#ctx.pid),
      {{gen, "List", [ElemT]}, {gen, "Set", [ElemT]}};
    Op == '$' -> {{con, "Char"}, {con, "Int"}};
    Op == '-' ->
      NumT = tv_server:fresh("Num", C1#ctx.pid),
      {NumT, NumT};
    Op == 'discard' -> {ExprT, none}
  end,

  C2 = add_cst(ExpExprT, ExprT, ?LOC(Expr), ?FROM_UNARY_OP(Op), C1),
  C3 = add_cst(ResultT, TV, Loc, ?FROM_OP_RESULT(Op), C2),
  {TV, C3}.

infer_sig(RestrictVs, Unique, Ifaces, Sig, C) ->
  C1 = C#ctx{ifaces=Ifaces},
  infer_sig_helper(RestrictVs, Unique, Sig, C1).

infer_sig_helper(RestrictVs, Unique, {lam_te, _, ArgTE, ReturnTE}, C) ->
  {ArgT, C1} = infer_sig_helper(RestrictVs, Unique, ArgTE, C),
  {ReturnT, C2} = infer_sig_helper(RestrictVs, Unique, ReturnTE, C1),
  {{lam, ArgT, ReturnT}, C2};
infer_sig_helper(RestrictVs, Unique, {tuple_te, _, ElemTEs}, C) ->
  {ElemTs, C1} = lists:mapfoldl(fun(TE, FoldC) ->
    infer_sig_helper(RestrictVs, Unique, TE, FoldC)
  end, C, ElemTEs),
  {{tuple, ElemTs}, C1};
infer_sig_helper(RestrictVs, Unique, {gen_te, Loc, ConToken, ParamTEs}, C) ->
  {con_token, _, RawCon} = ConToken,
  Con = qualify(RawCon, C),

  {Valid, C1} = case Unique of
    false -> validate_type(Con, length(ParamTEs), Loc, C);
    % We're inferring a new type, so don't do validation. Name conflicts for
    % new types are handled prior to beginning inference.
    true -> {true, C}
  end,

  {ParamTs, C2} = lists:mapfoldl(fun(TE, FoldC) ->
    infer_sig_helper(RestrictVs, Unique, TE, FoldC)
  end, C1, ParamTEs),

  if
    Valid -> {{gen, Con, ParamTs}, C2};
    true -> {tv_server:fresh(C2#ctx.pid), C2}
  end;
infer_sig_helper(RestrictVs, Unique, {tv_te, Loc, V, TE}, C) ->
  C1 = case RestrictVs of
    false -> C;
    {T, AllowedVs} ->
      case gb_sets:is_member(V, AllowedVs) of
        true -> C;
        false ->
          case T of
            % T is already an invalid type; no need to add another error
            {tv, _, _, _} -> C;
            _ -> add_ctx_err(?ERR_TV_SCOPE(V, element(2, T)), Loc, C)
          end
      end
  end,

  {I, C2} = case TE of
    % TODO: ensure this is a valid iface
    {none, _} -> {none, C1};
    {con_token, _, I_} -> {I_, C1};
    {record_te, _, _} ->
      {RecordT, CaseC} = infer_sig_helper(RestrictVs, Unique, TE, C1),
      {record, _, FieldMap} = RecordT,
      {FieldMap, CaseC}
  end,

  Ifaces = C2#ctx.ifaces,
  C3 = case maps:find(V, Ifaces) of
    {ok, ExpI} ->
      case {Unique, ExpI} of
        % TODO: include location of other TV
        {true, _} -> add_ctx_err(?ERR_REDEF_TV(V), Loc, C2);
        {false, I} -> C2;
        {false, _} ->
          % TODO: include location of other iface
          add_ctx_err(?ERR_TV_IFACE(V, ExpI, I), Loc, C2)
      end;
    error -> C2#ctx{ifaces=Ifaces#{V => I}}
  end,

  % This TV should be rigid in signatures, but it'll be reset to flex in
  % norm_sig_type. Hence, we don't set rigid here, but rather after renaming.
  {{tv, V, I, false}, C3};
infer_sig_helper(_, Unique, {con_token, Loc, RawCon}, C) ->
  Con = qualify(RawCon, C),
  {Valid, C1} = case Unique of
    false -> validate_type(Con, 0, Loc, C);
    % We're inferring a new type, so don't do validation. Name conflicts for
    % new types are handled prior to beginning inference.
    true -> {true, C}
  end,

  case Valid of
    true -> {{con, Con}, C1};
    false -> {tv_server:fresh(C1#ctx.pid), C1}
  end;
infer_sig_helper(RestrictVs, Unique, {record_te, _, Fields}, C) ->
  {FieldMap, C1} = lists:foldl(fun({Var, FieldTE}, {FoldMap, FoldC}) ->
    {var, Loc, Name} = Var,
    {FieldT, FoldC1} = infer_sig_helper(RestrictVs, Unique, FieldTE, FoldC),

    case maps:is_key(Name, FoldMap) of
      true -> {FoldMap, add_ctx_err(?ERR_DUP_FIELD(Name), Loc, FoldC1)};
      false -> {FoldMap#{Name => FieldT}, FoldC1}
    end
  end, {#{}, C}, Fields),

  {{record, tv_server:next_name(C1#ctx.pid), FieldMap}, C1};
infer_sig_helper(RestrictVs, Unique, {record_ext_te, Loc, BaseTE, Fields}, C) ->
  {BaseT, C1} = infer_sig_helper(RestrictVs, Unique, BaseTE, C),
  {{record, A, FieldMap}, C2} = infer_sig_helper(
    RestrictVs,
    Unique,
    {record_te, Loc, Fields},
    C1
  ),
  {{record_ext, A, BaseT, FieldMap}, C2};
infer_sig_helper(_, _, {none, _}, C) -> {none, C}.

qualify(RawCon, C) ->
  case maps:is_key(RawCon, C#ctx.types) of
    % built-in type
    true -> RawCon;

    false ->
      case string:chr(RawCon, $.) of
        0 -> lists:concat([C#ctx.module, '.', RawCon]);
        _ -> RawCon
      end
  end.

infer_pattern({var, Loc, Name}=Pattern, {fn, _, _, _}=Expr, From, C) ->
  {TV, ID} = tv_server:fresh_gnr_id(C#ctx.pid),
  C1 = env_add(Name, {add_dep, TV, ID}, false, C),
  {PatternT, C2} = infer(Pattern, new_gnr(TV, ID, C1)),
  {ExprT, C3} = infer(Expr, C2),

  % We add the expr constraint last to ensure it's unified first (constraints
  % are unified in reverse order). This prevents us from ever having to unify
  % a function application {lam, Loc, _, _} with another function app, since
  % every function created will first be unified with {lam, _, _}, which has no
  % Loc. It's a subtle change in ordering that gives us better error messages
  % for recursive functions that are given too many arguments.
  G3 = C3#ctx.gnr,
  G4 = G3#gnr{csts=G3#gnr.csts ++ [make_cst(PatternT, ExprT, Loc, From, C3)]},
  C4 = C3#ctx{gnr=G4},

  finish_gnr(C4, C#ctx.gnr);

infer_pattern(Pattern, Expr, From, C) ->
  {ExprT, C1} = infer(Expr, new_gnr(C)),
  {PatternT, C2} = infer(Pattern, with_pattern_env(Pattern, C1)),
  C3 = add_cst(PatternT, ExprT, ?LOC(Pattern), From, C2),
  finish_gnr(C3, C#ctx.gnr).

with_pattern_env(Pattern, C) ->
  ID = C#ctx.gnr#gnr.id,
  Names = pattern_names(Pattern),

  {Vs, C1} = gb_sets:fold(fun(Name, {FoldVs, FoldC}) ->
    TV = tv_server:fresh(C#ctx.pid),
    {tv, V, _, _} = TV,
    {[V | FoldVs], env_add(Name, {add_dep, TV, ID}, false, FoldC)}
  end, {[], C}, Names),

  C1#ctx{gnr=C1#ctx.gnr#gnr{vs=Vs}}.

pattern_names([]) -> gb_sets:new();
pattern_names([Node | Rest]) ->
  gb_sets:union(pattern_names(Node), pattern_names(Rest));
pattern_names({N, _, _}) when N == int; N == float; N == bool; N == char;
    N == str; N == atom; N == var_value; N == con_token ->
  gb_sets:new();
pattern_names({var, _, Name}) -> gb_sets:singleton(Name);
pattern_names({'_', _}) -> gb_sets:new();
pattern_names({field, _, ModuleConToken, ConToken}) ->
  gb_sets:union(pattern_names(ModuleConToken), pattern_names(ConToken));
pattern_names({app, _, ConToken, Args}) ->
  gb_sets:union(pattern_names(ConToken), pattern_names(Args));
pattern_names({list, _, Elems}) -> pattern_names(Elems);
pattern_names({cons, _, Elems, Tail}) ->
  gb_sets:union(pattern_names(Elems), pattern_names(Tail));
pattern_names({tuple, _, Elems}) -> pattern_names(Elems).

lookup(Module, Name, Loc, C) ->
  Key = {Module, Name},
  External = C#ctx.module /= Module,

  case maps:find(Key, C#ctx.env) of
    {ok, {_, false}} when External ->
      TV = tv_server:fresh(C#ctx.pid),
      {TV, add_ctx_err(?ERR_NOT_EXPORTED(Name, Module), Loc, C)};

    {ok, {{add_dep, EnvTV, ID}, _}} ->
      G = add_gnr_dep(ID, C#ctx.gnr),

      % We need to defer instantiation until we start solving constraints.
      % Otherwise, we don't know the real types of these variables, and can't
      % instantiate properly.
      {{inst, EnvTV}, C#ctx{gnr=G}};

    {ok, {{_, EnvTV}, _}} -> {EnvTV, C};

    error ->
      TV = tv_server:fresh(C#ctx.pid),
      C1 = if
        External -> add_ctx_err(?ERR_NOT_DEF(Name, Module), Loc, C);
        true -> add_ctx_err(?ERR_NOT_DEF(Name), Loc, C)
      end,
      {TV, C1}
  end.

env_exists(Name, C) ->
  Key = {C#ctx.module, Name},
  maps:is_key(Key, C#ctx.env).

env_get(Name, C) ->
  Key = {C#ctx.module, Name},
  {Value, _} = maps:get(Key, C#ctx.env),
  Value.

env_add(Name, Value, Exported, C) ->
  % just a sanity assertion that Value is in the right format
  case Value of
    {add_dep, {tv, _, _, _}, _} -> true;
    {no_dep, {tv, _, _, _}} -> true
  end,
  Key = {C#ctx.module, Name},
  C#ctx{env=(C#ctx.env)#{Key => {Value, Exported}}}.

env_remove(Name, C) ->
  Key = {C#ctx.module, Name},
  C#ctx{env=maps:remove(Key, C#ctx.env)}.

new_gnr(C) ->
  ID = tv_server:next_gnr_id(C#ctx.pid),
  G = #gnr{id=ID, vs=[], env=C#ctx.env, csts=[], deps=gb_sets:new()},
  C#ctx{gnr=G}.

new_gnr({tv, V, _, _}, ID, C) ->
  G = #gnr{id=ID, vs=[V], env=C#ctx.env, csts=[], deps=gb_sets:new()},
  C#ctx{gnr=G}.

finish_gnr(C, OldG) -> C#ctx{gnrs=[C#ctx.gnr | C#ctx.gnrs], gnr=OldG}.

add_gnr_dep(ID, G) -> G#gnr{deps=gb_sets:add(ID, G#gnr.deps)}.

add_cst(T1, T2, Loc, From, C) ->
  G = C#ctx.gnr,
  G1 = G#gnr{csts=[make_cst(T1, T2, Loc, From, C) | G#gnr.csts]},
  C#ctx{gnr=G1}.

make_cst(T1, T2, Loc, From, C) ->
  {T1, T2, C#ctx.module, Loc, From}.

validate_type(Con, NumParams, Loc, C) ->
  case maps:find(Con, C#ctx.types) of
    {ok, NumParams} -> {true, C};
    {ok, ExpNumParams} ->
      Msg = ?ERR_TYPE_PARAMS(Con, ExpNumParams, NumParams),
      {false, add_ctx_err(Msg, Loc, C)};
    % TODO: better messages when module is not defined (e.g. Bad.Type) and
    % module is defined but no such type exists (e.g. Module.Bad)
    error -> {false, add_ctx_err(?ERR_NOT_DEF_TYPE(Con), Loc, C)}
  end.

add_ctx_err(Msg, Loc, C) ->
  C#ctx{errs=[{Msg, C#ctx.module, Loc} | C#ctx.errs]}.

norm_sig_type(SigT, RigidVs, Pid) ->
  RigidVsSet = gb_sets:from_list(RigidVs),

  % TODO: is it more intuitive to change each fv to *fv and then replace?
  Subs = gb_sets:fold(fun(V, FoldSubs) ->
    case gb_sets:is_member(V, RigidVsSet) of
      true -> FoldSubs#{V => {rigid, tv_server:next_name(Pid)}};
      false -> FoldSubs#{V => tv_server:next_name(Pid)}
    end
  end, #{}, fvs(SigT)),

  % user can't input a type signature that needs record consolidation
  subs(SigT, Subs, #{}).

solve(Gs, S) ->
  Map = lists:foldl(fun(G, FoldMap) -> FoldMap#{G#gnr.id => G} end, #{}, Gs),
  %% ?LOG(
  %%   "Generalizations",
  %%   lists:map(fun(G) -> G#gnr{csts=pretty_csts(G#gnr.csts)} end, Gs)
  %% ),

  T = lists:foldl(fun(#gnr{id=ID}, FoldT) ->
    #{ID := #gnr{index=Index}} = FoldT#tarjan.map,
    if
      Index == undefined -> connect(ID, FoldT#tarjan{stack=[]});
      true -> FoldT
    end
  end, #tarjan{map=Map, next_index=0, solver=S}, Gs),

  case T#tarjan.solver of
    #solver{errs=Errs, subs=Subs, structs=Structs} when length(Errs) > 0 ->
      SubbedErrs = lists:map(fun
        ({T1, T2, Module, Loc, From}) ->
          SubbedT1 = subs(T1, Subs, Structs),
          SubbedT2 = subs(T2, Subs, Structs),

          IsRecord1 = is_tuple(SubbedT1) andalso (
            element(1, SubbedT1) == record orelse
            element(1, SubbedT1) == record_ext
          ),
          IsRecord2 = is_tuple(SubbedT2) andalso (
            element(1, SubbedT2) == record orelse
            element(1, SubbedT2) == record_ext
          ),

          {FinalT1, FinalT2} = case {IsRecord1, IsRecord2} of
            {true, false} -> {SubbedT1, unalias(SubbedT2, Structs)};
            {false, true} -> {unalias(SubbedT1, S#solver.structs), SubbedT2};
            _ -> {SubbedT1, SubbedT2}
          end,
          {FinalT1, FinalT2, Module, Loc, From};

        ({_, _, _}=Err) -> Err
      end, Errs),

      {errors, SubbedErrs};

    #solver{schemes=Schemes} -> {ok, Schemes}
  end.

connect(ID, #tarjan{stack=Stack, map=Map, next_index=NextIndex, solver=S}) ->
  #{ID := G} = Map,
  Stack1 = [ID | Stack],
  Map1 = Map#{ID := G#gnr{index=NextIndex, low_link=NextIndex, on_stack=true}},

  T1 = #tarjan{stack=Stack1, map=Map1, next_index=NextIndex + 1, solver=S},
  T2 = gb_sets:fold(fun(AdjID, FoldT) ->
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

      %% ?LOG("Solvable IDs", SolvableIDs),

      S3 = lists:foldl(fun(SolID, FoldS) ->
        #{SolID := SolG} = Map3,
        unify_csts(SolG, FoldS)
      end, S2, SolvableIDs),

      %% PrettySubs = maps:map(
      %%   fun
      %%     (_, {anchor, A}) -> ?FMT("anchor(~s)", [A]);
      %%     (_, T) -> pretty(T)
      %%   end,
      %%   S3#solver.subs
      %% ),
      %% ?LOG("Subs", PrettySubs),

      S4 = lists:foldl(fun(SolID, FoldS) ->
        #{SolID := SolG} = Map3,
        BoundVs = bound_vs(SolG#gnr.env, FoldS),

        lists:foldl(fun(SolV, NestedS) ->
          #solver{subs=Subs, structs=Structs, schemes=Schemes} = NestedS,
          SolTV = {tv, SolV, none, false},
          T = subs(SolTV, Subs, Structs),
          GVs = gb_sets:subtract(fvs(T), BoundVs),
          Schemes1 = Schemes#{SolV => {GVs, T}},
          NestedS#solver{schemes=Schemes1}
        end, FoldS, SolG#gnr.vs)
      end, S3, SolvableIDs),

      T2#tarjan{stack=tl(Left), map=Map3, solver=S4};

    true -> T2
  end.

unify_csts(#gnr{csts=Csts, env=Env}, S) ->
  BoundVs = bound_vs(Env, S),

  % Constraints are always prepended to the list in a depth-first manner. Hence,
  % the shallowest expression's constraints come first. We'd like to solve the
  % deepest expression's constraints first to have better error messages (e.g.
  % rather than can't unify Float with Bool, can't unify Set<Float> with
  % Set<Bool>), so we process the list in reverse order here.
  lists:foldr(fun({T1, T2, Module, Loc, From}, FoldS) ->
    ResolvedT1 = resolve(T1, FoldS),
    ResolvedT2 = resolve(T2, FoldS),
    #solver{subs=Subs, structs=Structs} = FoldS,

    SubbedT1 = shallow_subs(ResolvedT1, Subs, Structs),
    SubbedT2 = shallow_subs(ResolvedT2, Subs, Structs),
    FoldS1 = FoldS#solver{
      t1=SubbedT1,
      t2=SubbedT2,
      module=Module,
      loc=Loc,
      from=From
    },

    unify(SubbedT1, SubbedT2, FoldS1)
  end, S#solver{bound_vs=BoundVs}, Csts).

resolve({lam, ArgT, ReturnT}, S) ->
  {lam, resolve(ArgT, S), resolve(ReturnT, S)};
resolve({lam, Loc, ArgT, ReturnT}, S) ->
  {lam, Loc, resolve(ArgT, S), resolve(ReturnT, S)};
resolve({tuple, ElemTs}, S) ->
  {tuple, lists:map(fun(T) -> resolve(T, S) end, ElemTs)};
resolve({tv, V, I, Rigid}, _) -> {tv, V, I, Rigid};
resolve({con, Con}, _) -> {con, Con};
resolve({gen, Con, ParamTs}, S) ->
  {gen, Con, lists:map(fun(T) -> resolve(T, S) end, ParamTs)};
resolve({inst, TV}, S) ->
  {tv, V, _, _} = TV,
  ResolvedT = case maps:find(V, S#solver.schemes) of
    {ok, Scheme} -> inst(Scheme, S#solver.pid);
    error -> TV
  end,
  resolve(ResolvedT, S);
resolve({record, A, FieldMap}, S) ->
  {record, A, maps:map(fun(_, T) -> resolve(T, S) end, FieldMap)};
resolve({record_ext, A, BaseT, Ext}, S) ->
  ResolvedExt = maps:map(fun(_, T) -> resolve(T, S) end, Ext),
  {record_ext, A, resolve(BaseT, S), ResolvedExt};
resolve(none, _) -> none.

inst({GVs, T}, Pid) ->
  Subs = gb_sets:fold(fun(V, FoldSubs) ->
    FoldSubs#{V => tv_server:next_name(Pid)}
  end, #{}, GVs),
  % consolidation already happened when finalizing scheme
  subs(T, Subs, #{}).

unify(T1, T2, S) when T1 == T2 -> S;

unify({lam, ArgT1, ReturnT1}, {lam, ArgT2, ReturnT2}, S) ->
  S1 = sub_unify(ArgT1, ArgT2, S),
  sub_unify(ReturnT1, ReturnT2, S1);
unify({lam, Loc, ArgT1, ReturnT1}, {lam, ArgT2, ReturnT2}, S) ->
  #solver{loc=OrigLoc, t1=OrigT1, t2=OrigT2} = S,
  S1 = sub_unify(ArgT1, ArgT2, S#solver{loc=Loc, t1=ArgT1, t2=ArgT2}),
  sub_unify(ReturnT1, ReturnT2, S1#solver{loc=OrigLoc, t1=OrigT1, t2=OrigT2});
unify({lam, _, _}=T1, {lam, _, _, _}=T2, S) -> sub_unify(T2, T1, S);
unify({lam, _, _, _}=T1, {lam, _, ArgT2, ReturnT2}, S) ->
  sub_unify(T1, {lam, ArgT2, ReturnT2}, S);

unify({tuple, ElemTs1}, {tuple, ElemTs2}, S) ->
  if
    length(ElemTs1) /= length(ElemTs2) -> add_err(S);
    true ->
      lists:foldl(fun({T1, T2}, FoldS) ->
        sub_unify(T1, T2, FoldS)
      end, S, lists:zip(ElemTs1, ElemTs2))
  end;

unify({record, A1, FieldMap1}, {record, A2, FieldMap2}, S) ->
  Keys1 = gb_sets:from_list(maps:keys(FieldMap1)),
  Keys2 = gb_sets:from_list(maps:keys(FieldMap2)),

  if
    Keys1 /= Keys2 -> add_err(S);
    true ->
      S1 = gb_sets:fold(fun(Key, FoldS) ->
        sub_unify(maps:get(Key, FieldMap1), maps:get(Key, FieldMap2), FoldS)
      end, S, Keys1),

      case no_errs(S, S1) of
        true -> add_sub_anchor(A1, A2, S1);
        _ -> S1
      end
  end;

unify({record, A1, FieldMap}, {record_ext, A2, BaseT, Ext}, S) ->
  Keys = gb_sets:from_list(maps:keys(FieldMap)),
  KeysExt = gb_sets:from_list(maps:keys(Ext)),

  case gb_sets:is_subset(KeysExt, Keys) of
    true ->
      S1 = gb_sets:fold(fun(Key, FoldS) ->
        sub_unify(maps:get(Key, FieldMap), maps:get(Key, Ext), FoldS)
      end, S, KeysExt),

      RelaxedFieldMap = gb_sets:fold(fun(Key, FoldFieldMap) ->
        TV = tv_server:fresh(S#solver.pid),
        FoldFieldMap#{Key => TV}
      end, FieldMap, KeysExt),

      NewA = tv_server:next_name(S1#solver.pid),
      S2 = sub_unify(BaseT, {record, NewA, RelaxedFieldMap}, S1),

      case no_errs(S, S2) of
        true -> add_sub_anchor(A1, A2, S2);
        _ -> S2
      end;

    false -> add_err(S)
  end;
unify({record_ext, _, _, _}=T1, {record, _, _}=T2, S) ->
  sub_unify(T2, T1, S);

unify({record_ext, A1, BaseT1, Ext1}, {record_ext, A2, BaseT2, Ext2}, S) ->
  Keys1 = gb_sets:from_list(maps:keys(Ext1)),
  Keys2 = gb_sets:from_list(maps:keys(Ext2)),
  CommonKeys = gb_sets:intersection(Keys1, Keys2),

  {RelaxedExt1, RelaxedExt2, S1} = gb_sets:fold(fun(Key, Memo) ->
    {FoldExt1, FoldExt2, FoldS} = Memo,
    NewFoldExt1 = maps:remove(Key, FoldExt1),
    NewFoldExt2 = maps:remove(Key, FoldExt2),

    NewFoldS = sub_unify(maps:get(Key, Ext1), maps:get(Key, Ext2), FoldS),
    {NewFoldExt1, NewFoldExt2, NewFoldS}
  end, {Ext1, Ext2, S}, CommonKeys),

  % Note: At this point, for a successful type check, BaseT1 and BaseT2 must be
  % TVs. If they are full records or record_exts, they would have been
  % consolidated. It's possible they are invalid non-record types, at which
  % point they would've generated errors in the past, since each time we create
  % a record_ext type, we ensure the base is a record with the keys in ext.
  %
  % Consequently, if no keys differ between the extensions, we don't need to do
  % anything further; BaseT1 *should not* be unified with BaseT2, since they're
  % allowed to be different types without their extensions.
  %
  % If keys are included in one ext, but not the other, we must ensure they're
  % present in the opposite base.
  S2 = case maps:size(RelaxedExt2) of
    0 -> S1;
    _ ->
      NewA1 = tv_server:next_name(S#solver.pid),
      TV1 = tv_server:fresh(S#solver.pid),
      sub_unify(BaseT1, {record_ext, NewA1, TV1, RelaxedExt2}, S1)
  end,

  S3 = case maps:size(RelaxedExt1) of
    0 -> S2;
    _ ->
      NewA2 = tv_server:next_name(S#solver.pid),
      TV2 = tv_server:fresh(S#solver.pid),
      sub_unify(BaseT2, {record_ext, NewA2, TV2, RelaxedExt1}, S2)
  end,

  case no_errs(S, S3) of
    true -> add_sub_anchor(A1, A2, S3);
    _ -> S3
  end;

unify({tv, V1, I1, Rigid1}, {tv, V2, I2, Rigid2}, S) ->
  TV1 = {tv, V1, I1, Rigid1},
  TV2 = {tv, V2, I2, Rigid2},

  Bound1 = gb_sets:is_member(V1, S#solver.bound_vs),
  Bound2 = gb_sets:is_member(V2, S#solver.bound_vs),
  Occurs = occurs(V1, TV2, S) or occurs(V2, TV1, S),

  if
    Occurs -> add_err(S);

    not Rigid1, not Bound1, Rigid2 ->
      if
        I1 == none; I1 == I2 -> add_sub(V1, TV2, S);
        true -> add_err(S)
      end;

    not Rigid2, not Bound2, Rigid1 ->
      if
        I2 == none; I1 == I2 -> add_sub(V2, TV1, S);
        true -> add_err(S)
      end;

    not Rigid1, not Rigid2 ->
      if
        I1 == none; I1 == I2 -> add_sub(V1, TV2, S);
        I2 == none -> add_sub(V2, TV1, S);
        true -> add_err(S)
      end;

    true -> add_err(S)
  end;
unify({tv, V, I, Rigid}, T, S) ->
  Occurs = occurs(V, T, S),
  Instance = (I == none) or instance(T, I),
  Bound = gb_sets:is_member(V, S#solver.bound_vs),
  WouldEscape = Bound and occurs(true, T, S),

  if
    Occurs -> add_err(S);
    Rigid or WouldEscape -> add_err(S);
    Instance -> add_sub(V, T, S);
    true -> add_err(S)
  end;
unify(T, {tv, V, I, Rigid}, S) -> sub_unify({tv, V, I, Rigid}, T, S);

unify({gen, Con, ParamTs1}, {gen, Con, ParamTs2}, S) ->
  if
    length(ParamTs1) /= length(ParamTs2) -> add_err(S);
    true ->
      lists:foldl(fun({T1, T2}, FoldS) ->
        sub_unify(T1, T2, FoldS)
      end, S, lists:zip(ParamTs1, ParamTs2))
  end;

unify(T1, T2, S) when element(1, T2) == record; element(1, T2) == record_ext ->
  case unalias(T1, S#solver.structs) of
    T1 -> add_err(S);
    NewT1 ->
      S1 = sub_unify(NewT1, T2, S),
      if
        length(S#solver.errs) == length(S1#solver.errs) ->
          add_sub(element(2, T2), T1, S1);
        true -> S1
      end
  end;
unify(T1, T2, S) when element(1, T1) == record; element(1, T1) == record_ext ->
  sub_unify(T2, T1, S);

unify(T1, T2, S) ->
  case {unalias(T1, S#solver.structs), unalias(T2, S#solver.structs)} of
    % if only T1 or T2 needs to be unaliased, we've accounted for it above
    {T1, _} -> add_err(S);
    {_, T2} -> add_err(S);
    {NewT1, NewT2} -> sub_unify(NewT1, NewT2, S)
  end.

sub_unify(T1, T2, #solver{subs=Subs, structs=Structs}=S) ->
  unify(shallow_subs(T1, Subs, Structs), shallow_subs(T2, Subs, Structs), S).

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

add_sub_anchor(A1, A2, S) when A1 == none; A2 == none; A1 == A2 -> S;
add_sub_anchor(A1, A2, S) -> add_sub(A2, {anchor, A1}, S).

add_err(S) ->
  #solver{t1=T1, t2=T2, module=Module, loc=Loc, from=From} = S,
  Err = {T1, T2, Module, Loc, From},
  S#solver{errs=[Err | S#solver.errs]}.

no_errs(S1, S2) -> length(S1#solver.errs) == length(S2#solver.errs).

unalias({con, Con}, Structs) ->
  case maps:find(Con, Structs) of
    {ok, {_, [], RawFieldMap}} ->
      {record, none, RawFieldMap};
    error -> {con, Con}
  end;
unalias({gen, Con, ParamTs}, Structs) ->
  case maps:find(Con, Structs) of
    {ok, {_, Vs, RawFieldMap}} ->
      Subs = maps:from_list(lists:zip(Vs, ParamTs)),
      subs({record, none, RawFieldMap}, Subs, Structs);
    error -> {gen, Con, ParamTs}
  end;
unalias(T, _) -> T.

instance({con, "Int"}, "Num") -> true;
instance({con, "Float"}, "Num") -> true;
instance({con, "String"}, "Concatable") -> true;
instance({gen, "List", _}, "Concatable") -> true;
instance({gen, "Map", _}, "Concatable") -> true;
instance({gen, "Set", _}, "Concatable") -> true;
instance({gen, "List", _}, "Separable") -> true;
instance({gen, "Set", _}, "Separable") -> true;
instance(_, _) -> false.

subs({lam, ArgT, ReturnT}, Subs, Structs) ->
  {lam, subs(ArgT, Subs, Structs), subs(ReturnT, Subs, Structs)};
subs({lam, Loc, ArgT, ReturnT}, Subs, Structs) ->
  {lam, Loc, subs(ArgT, Subs, Structs), subs(ReturnT, Subs, Structs)};
subs({tuple, ElemTs}, Subs, Structs) ->
  {tuple, lists:map(fun(T) -> subs(T, Subs, Structs) end, ElemTs)};
subs({tv, _, _, _}=TV, Subs, Structs) ->
  case shallow_subs(TV, Subs, Structs) of
    TV -> TV;
    NewT -> subs(NewT, Subs, Structs)
  end;
subs({con, Con}, _, _) -> {con, Con};
subs({gen, Con, ParamTs}, Subs, Structs) ->
  {gen, Con, lists:map(fun(T) -> subs(T, Subs, Structs) end, ParamTs)};
subs({record, A, FieldMap}, Subs, Structs) ->
  case maps:find(A, Subs) of
    error ->
      NewFieldMap = maps:map(fun(_, T) ->
        subs(T, Subs, Structs)
      end, FieldMap),
      {record, A, NewFieldMap};
    {ok, {anchor, NewA}} -> subs({record, NewA, FieldMap}, Subs, Structs);
    {ok, T} -> subs(T, Subs, Structs)
  end;
subs({record_ext, A, BaseT, Ext}, Subs, Structs) ->
  case maps:find(A, Subs) of
    error ->
      NewBase = subs(BaseT, Subs, Structs),
      NewExt = maps:map(fun(_, T) -> subs(T, Subs, Structs) end, Ext),
      consolidate({record_ext, A, NewBase, NewExt}, Structs);
    {ok, {anchor, NewA}} ->
      subs({record_ext, NewA, BaseT, Ext}, Subs, Structs);
    {ok, T} -> subs(T, Subs, Structs)
  end;
subs(none, _, _) -> none.

shallow_subs({tv, V, I, Rigid}, Subs, Structs) ->
  case maps:find(V, Subs) of
    error -> {tv, V, I, Rigid};
    {ok, {rigid, V1}} -> {tv, V1, I, true};

    {ok, {set_iface, I1}} ->
      false = Rigid,
      {tv, V, I1, Rigid};

    {ok, Value} ->
      Sub = if
        % Replacing with a new type entirely
        is_tuple(Value) or (Value == none) -> Value;
        % Instantiation, so rigid resets to false
        true -> {tv, Value, I, false}
      end,
      shallow_subs(Sub, Subs, Structs)
  end;
shallow_subs({record, A, FieldMap}=T, Subs, Structs) ->
  case maps:find(A, Subs) of
    error -> T;
    {ok, {anchor, NewA}} ->
      shallow_subs({record, NewA, FieldMap}, Subs, Structs);
    {ok, NewT} -> shallow_subs(NewT, Subs, Structs)
  end;
shallow_subs({record_ext, A, BaseT, Ext}=T, Subs, Structs) ->
  case maps:find(A, Subs) of
    error -> consolidate(T, Structs);
    {ok, {anchor, NewA}} ->
      shallow_subs({record_ext, NewA, BaseT, Ext}, Subs, Structs);
    {ok, NewT} -> shallow_subs(NewT, Subs, Structs)
  end;
shallow_subs(T, _, _) -> T.

consolidate({record_ext, A, {record_ext, _, BaseT, Ext1}, Ext2}, Structs) ->
  consolidate({record_ext, A, BaseT, maps:merge(Ext1, Ext2)}, Structs);
consolidate({record_ext, A, {record, _, FieldMap}, Ext}, _) ->
  {record, A, maps:merge(FieldMap, Ext)};
consolidate({record_ext, A, BaseT, Ext}, Structs) ->
  case unalias(BaseT, Structs) of
    % invalid base; just return as is
    BaseT -> {record_ext, A, BaseT, Ext};
    NewBaseT -> consolidate({record_ext, A, NewBaseT, Ext}, Structs)
  end.

bound_vs(Env, #solver{subs=Subs, structs=Structs, schemes=Schemes}) ->
  maps:fold(fun(_, {Value, _}, FoldVs) ->
    case Value of
      {no_dep, T} -> gb_sets:union(FoldVs, fvs(subs(T, Subs, Structs)));

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
fvs({lam, _, ArgT, ReturnT}) -> fvs({lam, ArgT, ReturnT});
fvs({tuple, ElemTs}) ->
  lists:foldl(fun(T, FVs) ->
    gb_sets:union(FVs, fvs(T))
  end, gb_sets:new(), ElemTs);
fvs({tv, V, _, _}) -> gb_sets:singleton(V);
fvs({con, _}) -> gb_sets:new();
fvs({gen, _, ParamTs}) ->
  lists:foldl(fun(T, FVs) ->
    gb_sets:union(FVs, fvs(T))
  end, gb_sets:new(), ParamTs);
% fvs({inst, ...}) ommitted; they should be resolved
fvs({record, _, FieldMap}) ->
  maps:fold(fun(_, T, S) ->
    gb_sets:union(S, fvs(T))
  end, gb_sets:new(), FieldMap);
fvs({record_ext, _, BaseT, Ext}) ->
  gb_sets:union(fvs(BaseT), fvs({record, none, Ext}));
fvs(none) -> gb_sets:new().

occurs(V, T, #solver{subs=Subs, structs=Structs}) ->
  occurs(V, subs(T, Subs, Structs)).

occurs(V, {lam, ArgT, ReturnT}) ->
  occurs(V, ArgT) or occurs(V, ReturnT);
occurs(V, {lam, _, ArgT, ReturnT}) -> occurs(V, {lam, ArgT, ReturnT});
occurs(V, {tuple, ElemTs}) ->
  lists:foldl(fun(T, Occurs) ->
    Occurs or occurs(V, T)
  end, false, ElemTs);
occurs(V, {tv, V1, _, Rigid}) -> (V == Rigid) or (V == V1);
occurs(_, {con, _}) -> false;
occurs(V, {gen, _, ParamTs}) ->
  lists:foldl(fun(T, Occurs) ->
    Occurs or occurs(V, T)
  end, false, ParamTs);
% occurs({inst, ...}) ommitted; they should be resolved
occurs(V, {record, _, FieldMap}) ->
  maps:fold(fun(_, T, Occurs) ->
    Occurs or occurs(V, T)
  end, false, FieldMap);
occurs(V, {record_ext, _, BaseT, Ext}) ->
  occurs(V, BaseT) or occurs(V, {record, none, Ext});
occurs(_, none) -> false.

%% pretty_csts([]) -> [];
%% pretty_csts([{T1, T2, Module, Loc, From} | Rest]) ->
%%   [{pretty(T1), pretty(T2), Module, Loc, From} | pretty_csts(Rest)].

pretty({lam, ArgT, ReturnT}) ->
  Format = case ArgT of
    {lam, _, _} -> "(~s) -> ~s";
    {lam, _, _, _} -> "(~s) -> ~s";
    _ -> "~s -> ~s"
  end,
  ?FMT(Format, [pretty(ArgT), pretty(ReturnT)]);
pretty({lam, _, ArgT, ReturnT}) -> pretty({lam, ArgT, ReturnT});
pretty({tuple, ElemTs}) ->
  PrettyElemTs = lists:map(fun(T) -> pretty(T) end, ElemTs),
  ?FMT("(~s)", [string:join(PrettyElemTs, ", ")]);
pretty({tv, V, I, Rigid}) ->
  Str = if
    I == none -> tl(V);
    true -> ?FMT("~s: ~s", [tl(V), I])
  end,

  case Rigid of
    false -> Str;
    true -> ?FMT("rigid(~s)", [Str])
  end;
pretty({set_iface, I}) -> ?FMT("I = ~s", [I]);
% TODO: keep qualified when ambiguous
pretty({con, Con}) -> utils:unqualify(Con);
pretty({gen, "List", [ElemT]}) -> ?FMT("[~s]", [pretty(ElemT)]);
pretty({gen, Con, ParamTs}) ->
  PrettyParamTs = lists:map(fun(T) -> pretty(T) end, ParamTs),
  ?FMT("~s<~s>", [utils:unqualify(Con), string:join(PrettyParamTs, ", ")]);
pretty({inst, TV}) -> ?FMT("inst(~s)", [pretty(TV)]);
pretty({record, _, FieldMap}) -> ?FMT("{ ~s }", [pretty_field_map(FieldMap)]);
pretty({record_ext, _, BaseT, Ext}) ->
  ?FMT("{ ~s | ~s }", [pretty(BaseT), pretty_field_map(Ext)]);
pretty(none) -> "()".

pretty_field_map(FieldMap) ->
  FieldStrs = maps:fold(fun(Name, T, Strs) ->
    [?FMT("~s :: ~s", [Name, pretty(T)]) | Strs]
  end, [], FieldMap),
  string:join(lists:sort(FieldStrs), ", ").
