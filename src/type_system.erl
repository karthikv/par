-module(type_system).
-export([infer_file/1, infer_prg/1, pattern_names/1, unify/3]).
-on_load(load/0).
-include("common.hrl").

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
%   TV names.
% Env - a Name => T mapping of bindings in the environment.

% S - a solver record used to unify types and solve constraints
%   subs - the substitutions made to unify types
%   errs - any constraints that couldn't be unified
%   schemes - the schemes of env variables that have been solved for and
%     generalized
%   bound_vs - the set of TV names in the environment
%   inst_refs - a Ref => {T, SubbedVs} mapping of instantiated variables
%   iv_origins - a {I, V} => Origins mapping for Vs coming from inst vars
%   aliases - see aliases in ctx record
%   impls - a I => {RawT, InstT, Inits} mapping of impls
%   nested_ivs - a {I, V} => IVs mapping for impls depending on other impls
%   passed_vs - a V => {Is, ArgT, Module, Loc} mapping of Vs that have args
%               passed in for them
%   err_vs - a set of Vs that had errors unifying with a concrete type
%   gen_vs - a V => GenTVs mapping, where GenTVs all have base V
%   t1/t2 - the two types currently being unified
%   module - the module of the current constraint that's being unified
%   loc - the location of the current constraint that's being unified
%   from - a string describing where the current constraint is from
%   env - the env of the current gnr
%   pid - the process id of the TV server used to generated fresh TVs
-record(solver, {
  subs = #{},
  errs,
  schemes = #{},
  bound_vs,
  inst_refs = #{},
  iv_origins = #{},
  aliases,
  impls,
  nested_ivs = #{},
  passed_vs = [],
  err_vs = gb_sets:new(),
  gen_vs,
  t1,
  t2,
  module,
  loc,
  from,
  env,
  pid
}).

% G - a gnr record that represents a set of constraints to solve before
%     generalizing a type variable:
%   v - the TV name to generalize
%   env - see Env above
%   csts - an array of constraints to solve before generalizing
%   deps - a set of TV names corresponding to gnr records that need to solved
%     before this record or, in the case of (mutual) recursion,
%     simultaneously with this record
%   index / low_link / on_stack - bookkeeping for Tarjan's strongly connected
%     components algorithm; see T below and [1]
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
%     the TV name
%   stack / next_index - bookkeeping for Tarjan's algorithm; see [1]
%   solver - the solver record used for unification; see S below
%
% [1] https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm
-record(tarjan, {stack, map, next_index, solver}).

% options while performing substitution on a type
-record(sub_opts, {subs, aliases = #{}, for_err = false}).

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
  case parse_file(Path, #{}) of
    {ok, _, Comps, _} -> infer_comps(Comps);
    {errors, Errors, _} -> Errors
  end.

parse_file(RawPath, Parsed) ->
  Path = case filename:extension(RawPath) of
    "" -> utils:absolute(RawPath ++ ".par");
    _ -> utils:absolute(RawPath)
  end,

  case maps:find(Path, Parsed) of
    {ok, {module, Module}} -> {ok, Module, [], Parsed};
    {ok, skip} -> skip;

    error ->
      case file:read_file(Path) of
        {error, Reason} ->
          {errors, [{read_error, Path, Reason}], Parsed#{Path => skip}};

        {ok, Binary} ->
          Prg = binary_to_list(Binary),

          case parse_prg(Prg, Path) of
            {ok, Ast} ->
              {module, _, {con_token, _, Module}, Imports, _} = Ast,
              Parsed1 = Parsed#{Path => {module, Module}},

              Comp = #comp{module=Module, ast=Ast, path=Path, prg=Prg},
              Dir = filename:dirname(Path),

              {Deps, Comps, AllErrors, Parsed2} = lists:foldr(fun(Import, Memo) ->
                {import, _, {str, Loc, DepPath}, Idents} = Import,
                {FoldDeps, FoldComps, FoldAllErrors, FoldParsed} = Memo,

                FullPath = filename:join(Dir, binary_to_list(DepPath)),
                case parse_file(FullPath, FoldParsed) of
                  {ok, DepModule, DepComps, FoldParsed1} ->
                    {[{DepModule, Idents} | FoldDeps], [DepComps | FoldComps],
                     FoldAllErrors, FoldParsed1};

                  {errors, [{read_error, ImportPath, Reason}], FoldParsed1} ->
                    ImportError = {import_error, Loc, ImportPath, Reason, Comp},
                    {FoldDeps, FoldComps, [[ImportError] | FoldAllErrors],
                     FoldParsed1};

                  {errors, DepAllErrors, FoldParsed1} ->
                    {FoldDeps, FoldComps, [DepAllErrors | FoldAllErrors],
                     FoldParsed1};

                  skip -> Memo
                end
              end, {[], [], [], Parsed1}, Imports),

              case AllErrors of
                [_ | _] -> {errors, lists:append(AllErrors), Parsed2};
                _ ->
                  FullComp = Comp#comp{deps=Deps},
                  {ok, Module, lists:append([[FullComp] | Comps]), Parsed2}
              end;

            Errors -> {errors, [Errors], Parsed#{Path => skip}}
          end
      end
  end.

infer_prg(Prg) ->
  case parse_prg(Prg, "[infer-prg]") of
    {ok, Ast} ->
      % infer_prg should only be used only when there are no imports
      {module, _, {con_token, _, Module}, [], _} = Ast,
      %% ?LOG("Ast", Ast),

      Comp = #comp{
        module=Module,
        ast=Ast,
        deps=[],
        path="[infer-prg]",
        prg=Prg
      },
      infer_comps([Comp]);

    Errors -> Errors
  end.

parse_prg(Prg, Path) ->
  case 'Lexer':tokenize(Prg) of
    {errors, Errs} -> {lexer_errors, Errs, Path, Prg};
    {ok, Tokens} ->
      case 'Parser':parse(Tokens) of
        #{errs := [_ | _]=Errs} -> {parser_errors, Errs, Path, Prg};
        #{value := {some, Ast}} -> {ok, Ast}
      end
  end.

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

  C1 = populate_env_and_types(Comps, C),
  C2 = infer_defs(Comps, C1),
  S = #solver{
    errs=C2#ctx.errs,
    aliases=C2#ctx.aliases,
    impls=C2#ctx.impls,
    gen_vs=C2#ctx.gen_vs,
    pid=Pid
  },

  Result = case solve(C2#ctx.gnrs, S) of
    {ok, FinalS} ->
      #solver{
        schemes=Schemes,
        inst_refs=InstRefs,
        nested_ivs=NestedIVs
      } = FinalS,

      SubbedEnv = maps:map(fun(_, {Value, Exported}) ->
        {tv, V, _, _} = case Value of
          % TODO: would no_dep ever happen?
          {no_dep, TV} -> TV;
          {add_dep, TV, _} -> TV
        end,
        {inst(maps:get(V, Schemes), Pid), Exported}
      end, C2#ctx.env),

      SubbedInstRefsPairs = lists:filtermap(fun
        % In the case of a (mutually) recursive function, we defer computing the
        % SubbedVs until now, as we couldn't inst it earlier.
        ({Ref, {deferred, TV, Env}}) ->
          T = subs_s(TV, FinalS),
          BoundVs = bound_vs(Env, FinalS),
          IVs = utils:ivs(T, BoundVs),

          case IVs of
            [] -> false;
            _ ->
              SubbedVsPairs = lists:map(fun({Is, V}) ->
                % rigid doesn't matter here
                {V, {tv, V, Is, false}}
              end, IVs),
              {true, {Ref, {T, maps:from_list(SubbedVsPairs)}}}
          end;

        ({Ref, {T, SubbedVs}}) ->
          FinalSubbedVs = maps:map(fun(_, TV) ->
            subs_s(TV, FinalS)
          end, SubbedVs),

          % We want the original IVs to stay intact, so don't sub T.
          {true, {Ref, {T, FinalSubbedVs}}}
      end, maps:to_list(InstRefs)),
      SubbedInstRefs = maps:from_list(SubbedInstRefsPairs),

      SubbedFnRefs = maps:map(fun(_, {T, Env}) ->
        BoundVs = bound_vs(Env, FinalS),
        ArgTs = utils:arg_ts(subs_s(T, FinalS)),
        lists:map(fun(ArgT) -> utils:ivs(ArgT, BoundVs) end, ArgTs)
      end, C2#ctx.fn_refs),

      FinalC = C2#ctx{
        env=SubbedEnv,
        inst_refs=SubbedInstRefs,
        fn_refs=SubbedFnRefs,
        nested_ivs=NestedIVs
      },
      {ok, Comps, FinalC};

    {errors, Errs} -> {errors, Errs, Comps}
  end,

  % TODO: how to require that main is defined?
  ok = tv_server:stop(Pid),
  Result.

populate_env_and_types(Comps, C) ->
  lists:foldl(fun(Comp, FoldC) ->
    #comp{module=Module, ast={module, _, _, _, Defs}} = Comp,

    lists:foldl(fun(Node, ModuleC) ->
      case Node of
        {global, _, {var, Loc, Name}, _, Exported} ->
          {TV, ID} = tv_server:fresh_gnr_id(ModuleC#ctx.pid),
          define(Name, {add_dep, TV, ID}, Exported, Loc, ModuleC);

        {N, _, TE, OptionsOrFields} when N == enum; N == struct ->
          {Loc, Name, NumParams} = case TE of
            {con_token, Loc_, Name_} -> {Loc_, Name_, 0};
            {gen_te, _, {con_token, Loc_, Name_}, ParamTEs} ->
              {Loc_, Name_, length(ParamTEs)}
          end,

          Con = utils:qualify(Name, ModuleC),
          ModuleC1 = define_type(Con, false, NumParams, Loc, ModuleC),

          case N of
            enum ->
              Enums = ModuleC1#ctx.enums,
              {Variants, ModuleC2} = lists:mapfoldl(fun(Option, NestedC) ->
                {option, _, {con_token, OptionLoc, OptionCon}, _, _} = Option,
                {TV, ID} = tv_server:fresh_gnr_id(NestedC#ctx.pid),
                Value = {add_dep, TV, ID},
                {OptionCon, define(OptionCon, Value, true, OptionLoc, NestedC)}
              end, ModuleC1, OptionsOrFields),

              ModuleC2#ctx{enums=Enums#{Con => Variants}};

            struct ->
              {TV, ID} = tv_server:fresh_gnr_id(ModuleC1#ctx.pid),
              ModuleC2 = define(Name, {add_dep, TV, ID}, true, Loc, ModuleC1),

              {T, ModuleC3} = infer_sig(false, true, #{}, TE, ModuleC2),
              StructInfo = {T, ModuleC3#ctx.sig_vs},
              ModuleC3#ctx{structs=(ModuleC3#ctx.structs)#{Con => StructInfo}}
          end;

        {interface, _, {con_token, Loc, Name}, Fields} ->
          Con = utils:qualify(Name, ModuleC),
          NumParams = case gen_t_num_params({record_te, Loc, Fields}) of
            false -> 0;
            NumParams_ -> NumParams_
          end,
          ModuleC1 = define_type(Con, true, NumParams, Loc, ModuleC),

          NewIfaces = (ModuleC1#ctx.ifaces)#{Con => {Fields, none}},
          NewImpls = (ModuleC1#ctx.impls)#{Con => #{}},
          ModuleC2 = ModuleC1#ctx{ifaces=NewIfaces, impls=NewImpls},

          lists:foldl(fun({sig, _, {var, VarLoc, VarName}, _}, NestedC) ->
            {TV, ID} = tv_server:fresh_gnr_id(ModuleC#ctx.pid),
            define(VarName, {add_dep, TV, ID}, true, VarLoc, NestedC)
          end, ModuleC2, Fields);

        _ -> ModuleC
      end
    end, FoldC#ctx{module=Module}, Defs)
  end, C, Comps).

define(Name, Value, Exported, Loc, C) ->
  case env_exists(Name, C) of
    true -> add_ctx_err(?ERR_REDEF(Name), Loc, C);
    false -> env_add(Name, Value, Exported, C)
  end.

define_type(Con, IsIface, NumParams, Loc, C) ->
  Types = C#ctx.types,
  Builtin = string:chr(Con, $.) == 0,

  case maps:find(Con, Types) of
    {ok, {true, _}} ->
      if
        Builtin -> add_ctx_err(?ERR_REDEF_BUILTIN_IFACE(Con), Loc, C);
        true -> add_ctx_err(?ERR_REDEF_IFACE(Con), Loc, C)
      end;
    {ok, {false, _}} ->
      if
        Builtin -> add_ctx_err(?ERR_REDEF_BUILTIN_TYPE(Con), Loc, C);
        true -> add_ctx_err(?ERR_REDEF_TYPE(Con), Loc, C)
      end;
    error -> C#ctx{types=Types#{Con => {IsIface, NumParams}}}
  end.

gen_t_num_params({lam_te, _, ArgTE, ReturnTE}) ->
  case gen_t_num_params(ArgTE) of
    false -> gen_t_num_params(ReturnTE);
    NumParams -> NumParams
  end;
gen_t_num_params({tuple_te, _, ElemTEs}) ->
  lists:foldl(fun(ElemTE, FoldNumParams) ->
    case FoldNumParams of
      false -> gen_t_num_params(ElemTE);
      _ -> FoldNumParams
    end
  end, false, ElemTEs);
gen_t_num_params({gen_te, _, {tv_te, _, "T", _}, ParamTEs}) -> length(ParamTEs);
gen_t_num_params({gen_te, Loc, BaseTE, ParamTEs}) ->
  case gen_t_num_params(BaseTE) of
    false -> gen_t_num_params({tuple_te, Loc, ParamTEs});
    NumParams -> NumParams
  end;
gen_t_num_params({tv_te, _, "T", _}) -> 0;
gen_t_num_params({tv_te, _, _, _}) -> false;
gen_t_num_params({con_token, _, _}) -> false;
gen_t_num_params({record_te, _, Fields}) ->
  lists:foldl(fun({sig, _, _, TE}, FoldNumParams) ->
    case FoldNumParams of
      false -> gen_t_num_params(TE);
      _ -> FoldNumParams
    end
  end, false, Fields);
gen_t_num_params({record_ext_te, Loc, BaseTE, Fields}) ->
  case gen_t_num_params(BaseTE) of
    false -> gen_t_num_params({record_te, Loc, Fields});
    NumParams -> NumParams
  end;
gen_t_num_params({unit, _}) -> false.

infer_defs(Comps, C) ->
  lists:foldl(fun(Comp, FoldC) ->
    #comp{module=Module, ast={module, _, _, _, Defs}, deps=Deps} = Comp,
    DepModules = lists:map(fun({DepModule, _}) -> DepModule end, Deps),
    AccessibleModules = gb_sets:from_list([Module | DepModules]),

    FoldC1 = populate_direct_imports(
      Deps,
      FoldC#ctx{module=Module, modules=AccessibleModules}
    ),

    {LastSig, FoldC2} = lists:foldl(fun(Node, {UncheckedSig, ModuleC}) ->
      {Sig, ModuleC1} = if
        UncheckedSig == none -> {none, ModuleC};
        true ->
          {sig, _, {var, _, SigName}, _} = UncheckedSig,
          case Node of
            {global, _, {var, _, SigName}, _, _} -> {UncheckedSig, ModuleC};
            _ ->
              Err = ?ERR_SIG_NO_DEF(SigName),
              {none, add_ctx_err(Err, ?LOC(UncheckedSig), ModuleC)}
          end
      end,

      case Node of
        {global, _, {var, _, Name}, Expr, _} ->
          {add_dep, TV, ID} = env_get(Name, ModuleC1),
          ModuleC2 = case Expr of
            {fn, _, _, _, _} -> ModuleC1;
            _ -> env_remove(Name, ModuleC1)
          end,

          {ExprCstLoc, ExprCstFrom, ExprT, ModuleC3} = case Sig of
            none ->
              {ExprT_, ModuleC3_} = infer(Expr, new_gnr(TV, ID, ModuleC2)),
              {?LOC(Expr), ?FROM_GLOBAL_DEF(Name), ExprT_, ModuleC3_};

            % We'll generalize immediately after the sig and expr csts are
            % unified in a separate gnr.
            _ ->
              {ExprT_, ModuleC3_} = infer(Expr, new_gnr(ModuleC2)),
              {?LOC(Sig), ?FROM_GLOBAL_SIG(Name), ExprT_, ModuleC3_}
          end,

          % Unify expr constraint first for better error messages.
          ModuleC4 = append_csts(
            [make_cst(TV, ExprT, ExprCstLoc, ExprCstFrom, ModuleC3)],
            ModuleC3
          ),
          ModuleC5 = finish_gnr(ModuleC4, ModuleC2#ctx.gnr),
          ModuleC6 = ModuleC5#ctx{env=ModuleC#ctx.env},

          case Sig of
            none -> {none, ModuleC6};
            _ ->
              % There's no active gnr right now. Inferring a signature doesn't
              % add any constraints, so this is OK.
              {SigT, ModuleC7} = infer(Sig, ModuleC6),
              SigCst = make_cst(
                TV,
                SigT,
                ?LOC(Sig),
                ?FROM_GLOBAL_SIG(Name),
                ModuleC7
              ),

              ModuleC8 = infer_csts_first(
                [SigCst],
                ModuleC2#ctx.gnrs,
                [TV, ID],
                ModuleC7
              ),
              {none, ModuleC8}
          end;

        {sig, _, _, _} -> {Node, ModuleC1};

        _ ->
          {_, ModuleC2} = infer(Node, ModuleC1),
          {none, ModuleC2}
      end
    end, {none, FoldC1}, Defs),

    % Remove direct imports from env. We don't want modules trying to import
    % recursively through other modules, as this would make the order in
    % which files are processed important.
    FoldC3 = FoldC2#ctx{env=FoldC#ctx.env},

    case LastSig of
      none -> FoldC3;
      {sig, _, {var, _, SigName}, _} ->
        add_ctx_err(?ERR_SIG_NO_DEF(SigName), ?LOC(LastSig), FoldC3)
    end
  end, C, Comps).

populate_direct_imports(Deps, C) ->
  lists:foldl(fun({Module, Idents}, ModuleC) ->
    lists:foldl(fun(Ident, NestedC) ->
      case Ident of
        {var, Loc, Name} ->
          {Value, NestedC1} = raw_lookup(Module, Name, Loc, NestedC),
          define(Name, Value, false, Loc, NestedC1);

        {con_token, Loc, Name} ->
          Con = lists:concat([Module, '.', Name]),
          {TypeExists, NestedC1} = case maps:find(Con, NestedC#ctx.types) of
            {ok, {_, NumParams}} ->
              NewCon = utils:qualify(Name, NestedC),
              CaseC = case NumParams of
                0 -> add_alias(NewCon, [], {con, Con}, false, NestedC);
                _ ->
                  Vs = lists:map(fun(_) ->
                    tv_server:fresh(NestedC#ctx.pid)
                  end, lists:seq(1, NumParams)),

                  add_alias(NewCon, Vs, {gen, {con, Con}, Vs}, false, NestedC)
              end,
              {true, CaseC};

            error -> {false, NestedC}
          end,

          {Value, NestedC2} = raw_lookup(Module, Name, Loc, NestedC1),
          case {TypeExists, no_ctx_errs(NestedC2, NestedC1)} of
            {false, false} -> NestedC2;
            {true, false} -> NestedC1;
            {_, true} -> define(Name, Value, false, Loc, NestedC2)
          end;

        {variants, Loc, Name} ->
          Con = lists:concat([Module, '.', Name]),
          case maps:find(Con, NestedC#ctx.enums) of
            {ok, Variants} ->
              lists:foldl(fun(Variant, FoldC) ->
                Env = FoldC#ctx.env,
                {Value, true} = maps:get({Module, Variant}, Env),
                define(Variant, Value, false, Loc, FoldC)
              end, NestedC, Variants);

            error -> add_ctx_err(?ERR_NOT_DEF_TYPE(Con, Module), Loc, NestedC)
          end
      end
    end, ModuleC, Idents)
  end, C, Deps).

infer_csts_first(Csts, UntilGs, GnrArgs, C) ->
  % Unifying the expr and sig constraints first generally gives better
  % error messages. To do this, we create a new gnr containing just
  % these constraints, and make the necessary gnrs depend on it.
  C1 = case GnrArgs of
    [] -> new_gnr(C);
    [TV, ID] -> new_gnr(TV, ID, C)
  end,
  C2 = C1#ctx{gnr=C1#ctx.gnr#gnr{csts=Csts}},

  DepID = C2#ctx.gnr#gnr.id,
  UntilID = case UntilGs of
    [G | _] -> G#gnr.id;
    [] -> none
  end,

  {Gs, _} = lists:mapfoldl(fun(G, Done) ->
    case Done of
      true -> {G, Done};
      false ->
        case G#gnr.id of
          UntilID -> {G, true};
          _ -> {add_gnr_dep(DepID, G), false}
        end
    end
  end, false, C2#ctx.gnrs),
  finish_gnr(C2#ctx{gnrs=Gs}, C#ctx.gnr).

infer({fn, _, Ref, Args, Expr}, C) ->
  Names = gb_sets:union(lists:map(fun pattern_names/1, Args)),
  C1 = gb_sets:fold(fun(Name, FoldC) ->
    TV = tv_server:fresh(FoldC#ctx.pid),
    env_add(Name, {no_dep, TV}, false, FoldC)
  end, C, Names),

  {ArgTsRev, C2} = lists:foldl(fun(Pattern, {Ts, FoldC}) ->
    {PatternT, FoldC1} = infer(Pattern, FoldC),
    {[PatternT | Ts], FoldC1}
  end, {[], C1}, Args),

  {ReturnT, C3} = infer(Expr, C2),
  T = if
    length(Args) == 0 -> {lam, unit, ReturnT};
    true -> lists:foldl(fun(ArgT, LastT) ->
      {lam, ArgT, LastT}
    end, ReturnT, ArgTsRev)
  end,

  FnRefs = C3#ctx.fn_refs,
  % keep reference of original env to find bound variables
  C4 = C3#ctx{fn_refs=FnRefs#{Ref => {T, C#ctx.env}}},

  % restore original env
  {T, C4#ctx{env=C#ctx.env}};

infer({sig, _, _, Sig}, C) ->
  {SigT, C1} = infer_sig(false, false, #{}, Sig, C),
  {norm_sig_type(SigT, maps:keys(C1#ctx.sig_vs), C#ctx.pid), C1};

infer({binary_op, Loc, ':', Expr, Sig}, C) ->
  G = C#ctx.gnr,
  {TV, ID} = tv_server:fresh_gnr_id(C#ctx.pid),

  {ExprT, C1} = infer(Expr, new_gnr(TV, ID, C)),
  {SigT, C2} = infer_sig(false, false, #{}, Sig, C1),
  NormSigT = norm_sig_type(SigT, maps:keys(C2#ctx.sig_vs), C2#ctx.pid),

  C3 = add_cst(TV, ExprT, ?LOC(Expr), ?FROM_EXPR_SIG, C2),
  C4 = add_cst(TV, NormSigT, Loc, ?FROM_EXPR_SIG, C3),
  C5 = finish_gnr(C4, add_gnr_dep(ID, G)),

  % We don't want to return {inst, ...} directly; if it's added to two separate
  % constraints, that will cause two separate instantiations. Additionally, we
  % want all returned types to be fully resolved in case they're associated with
  % a reference. To accomplish this, introduce an intermediate TV that will get
  % assigned the inst. Note that from doesn't matter here; this constraint
  % should always succeed.
  InstTV = tv_server:fresh(C5#ctx.pid),
  % TODO: add a ref here
  C6 = add_cst(InstTV, {inst, none, TV}, Loc, ?FROM_INST, C5),

  {InstTV, C6};

infer({enum, _, EnumTE, Options}, C) ->
  {T, C1} = infer_sig(false, true, #{}, EnumTE, C),
  FVs = fvs(T),

  {_, C2} = lists:foldl(fun(Option, {Keys, FoldC}) ->
    {option, _, {con_token, Loc, Con}, ArgTEs, KeyNode} = Option,
    {ArgTsRev, FoldC1} = lists:foldl(fun(ArgTE, {Ts, NestedC}) ->
      {ArgT, NestedC1} = infer_sig(
        {T, FVs},
        false,
        NestedC#ctx.sig_vs,
        ArgTE,
        NestedC
      ),
      {[ArgT | Ts], NestedC1}
    end, {[], FoldC}, ArgTEs),

    OptionT = lists:foldl(fun(ArgT, LastT) ->
      {lam, ArgT, LastT}
    end, T, ArgTsRev),

    % don't need to make any Vs rigid; inst still works correctly
    NormOptionT = norm_sig_type(OptionT, [], FoldC1#ctx.pid),
    {add_dep, TV, ID} = env_get(Con, FoldC1),

    FoldC2 = new_gnr(TV, ID, FoldC1),
    FoldC3 = add_cst(TV, NormOptionT, Loc, ?FROM_ENUM_CTOR, FoldC2),
    FoldC4 = finish_gnr(FoldC3, FoldC1#ctx.gnr),

    case KeyNode of
      none ->
        Key = list_to_atom(Con),
        case maps:find(Key, Keys) of
          {ok, {default, _, _}} ->
            % we've already added an ERR_REDEF; no need to add another
            {Keys, FoldC4};
          {ok, {custom, _, CustomLoc}} ->
            % TODO: show actual code instead of just line for ERR_DUP_KEY
            FoldC5 = add_ctx_err(
              ?ERR_DUP_KEY(Key, Con, Loc),
              CustomLoc,
              FoldC4
            ),
            {Keys, FoldC5};
          error -> {Keys#{Key => {default, Con, Loc}}, FoldC4}
        end;

      {some, {atom, KeyLoc, Key}} ->
        case maps:find(Key, Keys) of
          {ok, {_, OtherCon, OtherLoc}} ->
            FoldC5 = add_ctx_err(
              ?ERR_DUP_KEY(Key, OtherCon, OtherLoc),
              KeyLoc,
              FoldC4
            ),

            % In case the map contains a default, we go ahead and replace the
            % value with a custom. This way, if another default comes up, we'll
            % correctly report an error.
            {Keys#{Key := {custom, Con, KeyLoc}}, FoldC5};
          error -> {Keys#{Key => {custom, Con, KeyLoc}}, FoldC4}
        end
    end
  end, {#{}, C1}, Options),

  {none, C2};

infer({struct, Loc, StructTE, Fields}, C) ->
  Name = case StructTE of
    {con_token, _, Name_} -> Name_;
    {gen_te, _, {con_token, _, Name_}, _} -> Name_
  end,
  Con = utils:qualify(Name, C),

  {T, SigIfaces} = maps:get(Con, C#ctx.structs),
  {{record, _, RawFieldMap}, C1} = infer_sig(
    {T, fvs(T)},
    false,
    SigIfaces,
    {record_te, Loc, Fields},
    C
  ),

  FnT = lists:foldr(fun({sig, _, {var, _, FieldName}, _}, LastT) ->
    #{FieldName := FieldT} = RawFieldMap,
    {lam, FieldT, LastT}
  end, T, Fields),

  % don't need to make any Vs rigid; inst still works correctly
  NormFnT = norm_sig_type(FnT, [], C1#ctx.pid),

  Vs = case T of
    {con, _} -> [];
    {gen, _, ParamTs} -> lists:map(fun({tv, V, none, _}) -> V end, ParamTs)
  end,
  C2 = add_alias(Con, Vs, {record, none, RawFieldMap}, true, C1),

  {add_dep, TV, ID} = env_get(Name, C2),
  C3 = new_gnr(TV, ID, C2),
  C4 = add_cst(TV, NormFnT, Loc, ?FROM_STRUCT_CTOR, C3),
  C5 = finish_gnr(C4, C2#ctx.gnr),

  {none, C5};

infer({interface, Loc, {con_token, _, RawCon}, Fields}, C) ->
  Con = utils:qualify(RawCon, C),
  {true, NumParams} = maps:get(Con, C#ctx.types),
  {RawRecordT, C1} = infer_sig(
    false,
    false,
    #{"T" => {none, NumParams}},
    {record_te, Loc, Fields},
    C
  ),

  Subs = #{"T" => {set_ifaces, gb_sets:from_list([Con])}},
  % type sigs don't need consolidation, so don't pass aliases
  {record, _, RawFieldMap} = subs(RawRecordT, #sub_opts{subs=Subs}),

  {FieldTs, C2} = lists:mapfoldl(fun(Sig, FoldC) ->
    {sig, SigLoc, {var, _, Name}, FieldTE} = Sig,
    FoldC1 = validate_iface_field(FieldTE, Name, SigLoc, FoldC),

    % don't need to make any Vs rigid; inst still works correctly
    #{Name := RawT} = RawFieldMap,
    T = norm_sig_type(RawT, [], FoldC1#ctx.pid),

    {add_dep, TV, ID} = env_get(Name, FoldC1),
    FoldC2 = new_gnr(TV, ID, FoldC1),
    FoldC3 = add_cst(TV, T, SigLoc, ?FROM_GLOBAL_SIG(Name), FoldC2),
    {RawT, finish_gnr(FoldC3, FoldC1#ctx.gnr)}
  end, C1, Fields),

  Ifaces = C2#ctx.ifaces,
  NewIfaces = Ifaces#{Con => setelement(2, maps:get(Con, Ifaces), FieldTs)},
  {none, C2#ctx{ifaces=NewIfaces}};

infer({impl, Loc, Ref, {con_token, IfaceLoc, RawIfaceCon}, ImplTE, Inits}, C) ->
  ImplLoc = ?LOC(ImplTE),
  IfaceCon = utils:resolve_con(RawIfaceCon, C),

  case maps:find(IfaceCon, C#ctx.ifaces) of
    % TODO: are builtin type classes implementable?
    error -> {none, add_ctx_err(?ERR_NOT_DEF_IFACE(IfaceCon), IfaceLoc, C)};

    {ok, {Fields, _}} ->
      {true, IfaceNumParams} = maps:get(IfaceCon, C#ctx.types),
      {RawT, C1} = case {IfaceNumParams, ImplTE} of
        {0, _} -> infer_sig(false, false, #{}, ImplTE, C);

        {_, {con_token, ConLoc, RawCon}} ->
          Con = utils:resolve_con(RawCon, C),
          NumParams = case maps:find(Con, C#ctx.types) of
            {ok, {_, Num}} when IfaceNumParams == 1 andalso Num > 0 -> Num;
            _ -> IfaceNumParams
          end,

          CaseC = validate_type(Con, false, NumParams, ConLoc, C),
          case no_ctx_errs(CaseC, C) of
            false -> {none, CaseC};
            true ->
              ParamTs = lists:map(fun(_) -> unit end, lists:seq(1, NumParams)),
              GenT = {gen, {con, Con}, ParamTs},
              {gen, ConT, _} = unalias_except_struct(GenT, CaseC#ctx.aliases),
              {ConT, CaseC}
          end;

        _ -> {none, add_ctx_err(?ERR_IMPL_TYPE(IfaceCon), ImplLoc, C)}
      end,

      case no_ctx_errs(C1, C) of
        false -> {none, C1};
        true ->
          ImplT = norm_sig_type(RawT, maps:keys(C1#ctx.sig_vs), C1#ctx.pid),
          Key = utils:impl_key(RawT),
          Impls = C1#ctx.impls,
          SubImpls = maps:get(IfaceCon, Impls),

          C2 = case maps:find(Key, SubImpls) of
            {ok, {ExistingT, _, _, _}} ->
              DupErr = ?ERR_DUP_IMPL(IfaceCon, Key, utils:pretty(ExistingT)),
              add_ctx_err(DupErr, ImplLoc, C1);
            error ->
              Value = {RawT, ImplT, Inits, C1#ctx.module},
              NewSubImpls = SubImpls#{Key => Value},
              C1#ctx{impls=Impls#{IfaceCon => NewSubImpls}}
          end,

          % TODO: is there a way around inferring these sigs again?
          {Pairs, C3} = lists:mapfoldl(fun(Sig, FoldC) ->
            {sig, SigLoc, {var, _, Name}, SigTE} = Sig,
            {SigT, FoldC1} = infer_sig(
              false,
              false,
              #{"T" => {none, IfaceNumParams}},
              SigTE,
              FoldC
            ),
            {{Name, {SigLoc, SigT}}, FoldC1}
          end, C2, Fields),

          % don't duplicate errors, as we've already inferred this signature
          C4 = C3#ctx{errs=C2#ctx.errs},
          FieldLocTs = maps:from_list(Pairs),

          {ActualNames, C5} = infer_impl_inits(
            Inits,
            ImplT,
            ImplLoc,
            IfaceCon,
            IfaceNumParams,
            FieldLocTs,
            C4
          ),

          ExpNames = gb_sets:from_list(maps:keys(FieldLocTs)),
          MissingNames = gb_sets:difference(ExpNames, ActualNames),

          C6 = gb_sets:fold(fun(Name, FoldC) ->
            add_ctx_err(?ERR_MISSING_FIELD_IMPL(Name, IfaceCon), Loc, FoldC)
          end, C5, MissingNames),
          ImplRefs = C6#ctx.impl_refs,
          {none, C6#ctx{impl_refs=ImplRefs#{Ref => Key}}}
      end
  end;

infer({unit, _}, C) -> {unit, C};
infer({int, _, _}, C) -> {tv_server:fresh("Num", C#ctx.pid), C};
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

  {{gen, {con, "List"}, [TV]}, C1};

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

  {{gen, {con, "Map"}, [KeyTV, ValueTV]}, C1};

infer({N, Loc, Name}, C) when N == var; N == con_token; N == var_value ->
  lookup(C#ctx.module, Name, Loc, none, C);

infer({var_ref, Loc, Ref, Name}, C) -> lookup(C#ctx.module, Name, Loc, Ref, C);

% only occurs when pattern matching to designate anything
infer({'_', _}, C) -> {tv_server:fresh(C#ctx.pid), C};

infer({anon_record, _, Inits}, C) ->
  {FieldMap, C1} = lists:foldl(fun(Init, {Map, FoldC}) ->
    {init, _, {var, Loc, Name}, Expr} = Init,

    {T, FoldC1} = case Expr of
      {fn, FnLoc, _, _, _} ->
        TV = tv_server:fresh(FoldC#ctx.pid),
        CaseC = env_add(Name, {no_dep, TV}, false, FoldC),
        {ExprT, CaseC1} = infer(Expr, CaseC),

        % TODO: should this cst be unified first for better error messages?
        CaseC2 = add_cst(TV, ExprT, FnLoc, ?FROM_FIELD_DEF(Name), CaseC1),
        {TV, CaseC2#ctx{env=FoldC#ctx.env}};

      _ -> infer(Expr, FoldC)
    end,

    case maps:is_key(Name, Map) of
      true -> {Map, add_ctx_err(?ERR_DUP_FIELD(Name), Loc, FoldC1)};
      false -> {Map#{Name => T}, FoldC1}
    end
  end, {#{}, C}, Inits),

  {{record, tv_server:next_name(C1#ctx.pid), FieldMap}, C1};

infer({anon_record_ext, Loc, Expr, AllInits}, C) ->
  {ExprT, C1} = infer(Expr, C),
  {Inits, ExtInits} = lists:foldl(fun(InitOrExt, Memo) ->
    {FoldInits, FoldExtInits} = Memo,
    case element(1, InitOrExt) of
      ext -> {FoldInits, [setelement(1, InitOrExt, init) | FoldExtInits]};
      init -> {[InitOrExt | FoldInits], FoldExtInits}
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

infer({record, Loc, {con_token, ConLoc, RawCon}, Inits}, C) ->
  Con = utils:resolve_con(RawCon, C),
  case maps:find(Con, C#ctx.types) of
    {ok, {false, NumParams}} ->
      ExpT = case NumParams of
        % if we've directly imported a struct type and are creating it here,
        % we need to unalias
        0 -> unalias_except_struct({con, Con}, C#ctx.aliases);
        _ ->
          Vs = lists:map(fun(_) ->
            tv_server:fresh(C#ctx.pid)
          end, lists:seq(1, NumParams)),
          unalias_except_struct({gen, {con, Con}, Vs}, C#ctx.aliases)
      end,

      {RecordT, C1} = infer({anon_record, Loc, Inits}, C),
      From = ?FROM_RECORD_CREATE(Con),

      TV = tv_server:fresh(C1#ctx.pid),
      C2 = add_cst(TV, RecordT, Loc, From, C1),
      C3 = add_cst(TV, ExpT, Loc, From, C2),
      {TV, C3};

    {ok, {true, _}} ->
      {RecordT, C1} = infer({anon_record, Loc, Inits}, C),
      {RecordT, add_ctx_err(?ERR_IFACE_NOT_TYPE(Con), ConLoc, C1)};

    error ->
      {RecordT, C1} = infer({anon_record, Loc, Inits}, C),
      {RecordT, add_ctx_err(?ERR_NOT_DEF_TYPE(Con), ConLoc, C1)}
  end;

infer({record_ext, Loc, {con_token, ConLoc, RawCon}, Expr, AllInits}, C) ->
  Con = utils:resolve_con(RawCon, C),
  case maps:find(Con, C#ctx.types) of
    {ok, {false, NumParams}} ->
      ExpT = case NumParams of
        0 -> unalias_except_struct({con, Con}, C#ctx.aliases);
        _ ->
          Vs = lists:map(fun(_) ->
            tv_server:fresh(C#ctx.pid)
          end, lists:seq(1, NumParams)),
          unalias_except_struct({gen, {con, Con}, Vs}, C#ctx.aliases)
      end,

      {RecordT, C1} = infer({anon_record_ext, Loc, Expr, AllInits}, C),
      From = ?FROM_RECORD_UPDATE,

      TV = tv_server:fresh(C1#ctx.pid),
      C2 = add_cst(TV, RecordT, Loc, From, C1),
      C3 = add_cst(TV, ExpT, Loc, From, C2),
      {TV, C3};

    {ok, {true, _}} ->
      {RecordT, C1} = infer({anon_record_ext, Loc, Expr, AllInits}, C),
      {RecordT, add_ctx_err(?ERR_IFACE_NOT_TYPE(Con), ConLoc, C1)};

    error ->
      {RecordT, C1} = infer({anon_record_ext, Loc, Expr, AllInits}, C),
      {RecordT, add_ctx_err(?ERR_NOT_DEF_TYPE(Con), ConLoc, C1)}
  end;

infer({field_fn, _, {var, _, Name}}, C) ->
  FieldTV = tv_server:fresh(C#ctx.pid),
  BaseTV = tv_server:fresh(C#ctx.pid),
  A = tv_server:next_name(C#ctx.pid),
  RecordExtT = {record_ext, A, BaseTV, #{Name => FieldTV}},
  {{lam, RecordExtT, FieldTV}, C};

% TODO: ensure this is parsed correctly or add error cases (e.g. when var is
% a con_token, expr must be a con_token)
infer({field, Loc, Expr, Prop}, C) ->
  case Expr of
    {con_token, ConLoc, Module} ->
      {Ref, Name} = case Prop of
        {var_ref, _, Ref_, Name_} -> {Ref_, Name_};
        {con_token, _, Name_} -> {none, Name_}
      end,

      case gb_sets:is_member(Module, C#ctx.modules) of
        true -> lookup(Module, Name, Loc, Ref, C);
        false ->
          TV = tv_server:fresh(C#ctx.pid),
          {TV, add_ctx_err(?ERR_NOT_DEF_MODULE(Module), ConLoc, C)}
      end;

    _ ->
      {ExprT, C1} = infer(Expr, C),
      {var, PropLoc, Name} = Prop,
      FieldFn = {field_fn, PropLoc, Prop},
      {{lam, RecordExtT, ResultT}, C2} = infer(FieldFn, C1),

      From = ?FROM_FIELD_ACCESS(Name),
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
    length(ArgLocTsRev) == 0 -> {lam, unit, TV};
    true ->
      lists:foldl(fun({ArgLoc, ArgT}, LastT) ->
        {lam, C2#ctx.env, ArgLoc, ArgT, LastT}
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
    Arity == 0 -> {lam, unit, tv_server:fresh(C1#ctx.pid)};
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
    {unit, _} -> {unit, C3};
    _ ->
      {ElseT, C4} = infer(Else, C3),
      TV = tv_server:fresh(C#ctx.pid),
      C5 = add_cst(TV, ThenT, ?LOC(Then), ?FROM_THEN_BODY, C4),
      C6 = add_cst(TV, ElseT, ?LOC(Else), ?FROM_ELSE_BODY, C5),
      {TV, C6}
  end;

infer({'let', _, Bindings, Then}, C) ->
  C1 = lists:foldl(fun({binding, _, Pattern, Expr}, FoldC) ->
    infer_pattern(Pattern, Expr, ?FROM_LET, FoldC)
  end, C, Bindings),

  {T, C2} = infer(Then, C1),
  {T, C2#ctx{env=C#ctx.env}};

infer({if_let, _, Pattern, Expr, Then, Else}, C) ->
  C1 = infer_pattern(Pattern, Expr, ?FROM_IF_LET_PATTERN, C),
  {ThenT, C2} = infer(Then, C1),
  % revert env to before pattern was parsed
  C3 = C2#ctx{env=C#ctx.env},

  case Else of
    {unit, _} -> {unit, C3};
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

  C1 = lists:foldl(fun({'case', _, Pattern, Then}, FoldC) ->
    {ExprT, FoldC1} = infer(Expr, new_gnr(FoldC)),
    ID = FoldC1#ctx.gnr#gnr.id,
    {PatternT, FoldC2} = infer(Pattern, with_pattern_env(Pattern, FoldC1)),
    FoldC3 = add_cst(
      ExprT,
      PatternT,
      ?LOC(Pattern),
      ?FROM_MATCH_PATTERN,
      FoldC2
    ),

    FoldC4 = finish_gnr(FoldC3, add_gnr_dep(ID, FoldC#ctx.gnr)),
    {ThenT, FoldC5} = infer(Then, FoldC4),
    % revert env to before pattern was parsed
    FoldC6 = FoldC5#ctx{env=FoldC#ctx.env},
    add_cst(TV, ThenT, ?LOC(Then), ?FROM_MATCH_BODY, FoldC6)
  end, C, Cases),

  {TV, C1};

infer({block, _, Exprs}, C) ->
  {T, C1} = lists:foldl(fun(Expr, {_, FoldC}) ->
    infer(Expr, FoldC)
  end, {unit, C}, Exprs),
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
      {{gen, {con, "List"}, [ElemT]}, {gen, {con, "Set"}, [ElemT]}};
    Op == '$' -> {{con, "Char"}, {con, "Int"}};
    Op == '-' ->
      NumT = tv_server:fresh("Num", C1#ctx.pid),
      {NumT, NumT};
    Op == 'discard' -> {ExprT, unit}
  end,

  C2 = add_cst(ExpExprT, ExprT, ?LOC(Expr), ?FROM_UNARY_OP(Op), C1),
  C3 = add_cst(ResultT, TV, Loc, ?FROM_OP_RESULT(Op), C2),
  {TV, C3}.

infer_sig(RestrictVs, Unique, SigVs, Sig, C) ->
  C1 = C#ctx{sig_vs=SigVs},
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
infer_sig_helper(RestrictVs, Unique, {gen_te, Loc, BaseTE, ParamTEs}, C) ->
  NumParams = length(ParamTEs),

  {BaseT, Is, C1} = case BaseTE of
    {con_token, _, RawCon} ->
      Con = utils:resolve_con(RawCon, C),
      CaseC = case Unique of
        false -> validate_type(Con, false, NumParams, Loc, C);
        % We're inferring a new type, so don't do validation. Name conflicts for
        % new types are handled prior to beginning inference.
        true -> C
      end,
      {{con, Con}, none, CaseC};

    {tv_te, TVLoc, V, Ifaces} ->
      {BaseIfaces, GenIs} = case Ifaces of
        [] -> {[], none};
        _ ->
          {BaseIfaces_, GenIsSet} = lists:foldr(fun(ConToken, Memo) ->
            {FoldBaseIfaces, FoldGenIsSet} = Memo,
            {con_token, _, RawI} = ConToken,
            I = utils:resolve_con(RawI, C),

            case maps:find(I, C#ctx.types) of
              {ok, {true, 0}} -> {FoldBaseIfaces, gb_sets:add(I, FoldGenIsSet)};
              _ -> {[ConToken | FoldBaseIfaces], FoldGenIsSet}
            end
          end, {[], gb_sets:new()}, Ifaces),

          GenIs_ = case gb_sets:is_empty(GenIsSet) of
            true -> none;
            false -> GenIsSet
          end,
          {BaseIfaces_, GenIs_}
      end,

      CaseC = C#ctx{num_params=NumParams},
      {BaseT_, CaseC1} = infer_sig_helper(
        RestrictVs,
        Unique,
        {tv_te, TVLoc, V, BaseIfaces},
        CaseC
      ),
      {BaseT_, GenIs, CaseC1#ctx{num_params=undefined}}
  end,
  Valid = no_ctx_errs(C, C1),

  {ParamTs, C2} = lists:mapfoldl(fun(TE, FoldC) ->
    infer_sig_helper(RestrictVs, Unique, TE, FoldC)
  end, C1, ParamTEs),

  if
    Valid ->
      T = case BaseT of
        {tv, _, _, _} ->
          NewV = tv_server:next_name(C2#ctx.pid),
          {gen, NewV, Is, BaseT, ParamTs};

        _ -> unalias_except_struct({gen, BaseT, ParamTs}, C2#ctx.aliases)
      end,
      {T, C2};

    true -> {tv_server:fresh(C2#ctx.pid), C2}
  end;
infer_sig_helper(RestrictVs, Unique, {tv_te, Loc, V, Ifaces}, C) ->
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

  NumParams = case C1#ctx.num_params of
    undefined -> 0;
    NumParams_ -> NumParams_
  end,

  {Is, C2} = case Ifaces of
    [] -> {none, C1};
    _ ->
      lists:foldl(fun({con_token, ConLoc, RawI_}, {FoldIs, FoldC}) ->
        I = utils:resolve_con(RawI_, C1),
        NewFoldIs = gb_sets:add(I, FoldIs),
        {NewFoldIs, validate_type(I, true, NumParams, ConLoc, FoldC)}
      end, {gb_sets:new(), C1}, Ifaces)
  end,

  case no_ctx_errs(C1, C2) of
    true ->
      SigVs = C2#ctx.sig_vs,
      C3 = case maps:find(V, SigVs) of
        {ok, {ExpIs, ExpNumParams}} ->
          if
            Unique -> add_ctx_err(?ERR_REDEF_TV(V), Loc, C2);
            ExpIs /= Is ->
              % TODO: include location of other v w/ iface
              add_ctx_err(?ERR_TV_IFACE(V, ExpIs, Is), Loc, C2);
            ExpNumParams /= NumParams ->
              % TODO: include location of other v w/ params
              add_ctx_err(?ERR_TV_NUM_PARAMS(V, ExpNumParams, NumParams), Loc, C2);
            true -> C2
          end;

        error -> C2#ctx{sig_vs=SigVs#{V => {Is, NumParams}}}
      end,

      % This TV should be rigid in signatures, but it'll be reset to flex in
      % norm_sig_type. Hence, we don't set rigid here.
      {{tv, V, Is, false}, C3};

    false -> {{tv, V, none, false}, C2}
  end;
infer_sig_helper(_, Unique, {con_token, Loc, RawCon}, C) ->
  Con = utils:resolve_con(RawCon, C),
  C1 = case Unique of
    false -> validate_type(Con, false, 0, Loc, C);
    % We're inferring a new type, so don't do validation. Name conflicts for
    % new types are handled prior to beginning inference.
    true -> C
  end,

  case no_ctx_errs(C, C1) of
    true -> {unalias_except_struct({con, Con}, C1#ctx.aliases), C1};
    false -> {tv_server:fresh(C1#ctx.pid), C1}
  end;
infer_sig_helper(RestrictVs, Unique, {record_te, _, Fields}, C) ->
  {FieldMap, C1} = lists:foldl(fun({sig, _, Var, FieldTE}, {FoldMap, FoldC}) ->
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
infer_sig_helper(_, _, {unit, _}, C) -> {unit, C}.

infer_pattern({var, Loc, Name}=Pattern, {fn, _, _, _, _}=Expr, From, C) ->
  {TV, ID} = tv_server:fresh_gnr_id(C#ctx.pid),
  C1 = env_add(Name, {add_dep, TV, ID}, false, C),
  {PatternT, C2} = infer(Pattern, new_gnr(TV, ID, C1)),
  {ExprT, C3} = infer(Expr, C2),
  C4 = add_cst(PatternT, ExprT, Loc, From, C3),
  finish_gnr(C4, add_gnr_dep(ID, C#ctx.gnr));

infer_pattern(Pattern, Expr, From, C) ->
  {ExprT, C1} = infer(Expr, new_gnr(C)),
  ID = C1#ctx.gnr#gnr.id,
  {PatternT, C2} = infer(Pattern, with_pattern_env(Pattern, C1)),

  C3 = add_cst(PatternT, ExprT, ?LOC(Pattern), From, C2),
  finish_gnr(C3, add_gnr_dep(ID, C#ctx.gnr)).

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

lookup(Module, Name, Loc, Ref, C) ->
  {Value, C1} = raw_lookup(Module, Name, Loc, C),
  case Value of
    {add_dep, TV, ID} ->
      C2 = C1#ctx{gnr=add_gnr_dep(ID, C1#ctx.gnr)},

      % We don't want to return {inst, ...} directly; if it's added to two
      % separate constraints, that will cause two separate instantiations.
      % Additionally, we want all returned types to be fully resolved in case
      % they're associated with a reference. To accomplish this, introduce an
      % intermediate TV that will get assigned the inst. Note that from doesn't
      % matter here; this constraint should always succeed.
      InstTV = tv_server:fresh(C2#ctx.pid),
      C3 = add_cst(InstTV, {inst, Ref, TV}, Loc, ?FROM_INST, C2),

      % We need to defer instantiation until we start solving constraints.
      % Otherwise, we don't know the real types of these variables, and can't
      % instantiate properly.
      {InstTV, C3};

    {no_dep, TV} -> {TV, C1}
  end.

raw_lookup(Module, Name, Loc, C) ->
  Key = {Module, Name},
  External = C#ctx.module /= Module,

  case maps:find(Key, C#ctx.env) of
    {ok, {Value, false}} when External ->
      {Value, add_ctx_err(?ERR_NOT_EXPORTED(Name, Module), Loc, C)};

    {ok, {Value, _}} -> {Value, C};

    error ->
      TV = tv_server:fresh(C#ctx.pid),
      C1 = if
        External -> add_ctx_err(?ERR_NOT_DEF(Name, Module), Loc, C);
        true -> add_ctx_err(?ERR_NOT_DEF(Name), Loc, C)
      end,
      {{no_dep, TV}, C1}
  end.

infer_impl_inits(
  Inits,
  ImplT,
  ImplLoc,
  IfaceCon,
  IfaceNumParams,
  FieldLocTs,
  C
) ->
  lists:foldl(fun(Init, {Names, FoldC}) ->
    {init, _, {var, VarLoc, Name}, Expr} = Init,

    case gb_sets:is_member(Name, Names) of
      true ->
        {Names, add_ctx_err(?ERR_DUP_FIELD_IMPL(Name), VarLoc, FoldC)};

      false ->
        NewNames = gb_sets:add(Name, Names),
        NewC = case maps:find(Name, FieldLocTs) of
          error ->
            add_ctx_err(?ERR_EXTRA_FIELD_IMPL(Name, IfaceCon), VarLoc, FoldC);

          {ok, {SigLoc, RawSigT}} ->
            {TupleSubs, NumParams} = case IfaceNumParams of
              1 ->
                {con, ImplCon} = ImplT,
                {_, NumParams_} = maps:get(ImplCon, C#ctx.types),

                TupleSubs_ = if
                  NumParams_ /= 1 ->
                    lists:foldl(fun({_, {gen, _, _, _, [ParamT]}}, FoldSubs) ->
                      ElemTs = lists:map(fun(_) ->
                        tv_server:fresh(FoldC#ctx.pid)
                      end, lists:seq(1, NumParams_)),

                      case ParamT of
                        {tv, V, _, _} -> FoldSubs#{V => {tuple, ElemTs}};
                        _ -> FoldSubs
                      end
                    end, #{}, gen_vs_list(RawSigT));

                  true -> #{}
                end,
                {TupleSubs_, NumParams_};

              _ -> {#{}, IfaceNumParams}
            end,

            TupleSigT = subs(RawSigT, #sub_opts{subs=TupleSubs}),
            FVs = gb_sets:delete_any("T", fvs(TupleSigT)),
            RigidVs = gb_sets:to_list(FVs),

            NormT = norm_sig_type(TupleSigT, RigidVs, FVs, FoldC#ctx.pid),
            NewV = tv_server:next_name(FoldC#ctx.pid),
            NewTV = {tv, NewV, none, false},
            % type sigs don't need consolidation, so don't pass aliases
            SigT = subs(NormT, #sub_opts{subs=#{"T" => NewV}}),

            % All IVs within ImplT will be in the environment during code gen.
            % To make sure they're treated as bound variables, whose impls
            % shouldn't be passed to the Expr here, we add ImplT in the env
            % under some fake variable name.
            FoldC1 = new_gnr(env_add("_@Impl", {no_dep, ImplT}, false, FoldC)),

            FoldC2 = case IfaceNumParams of
              0 -> add_cst(NewTV, ImplT, ImplLoc, ?FROM_IMPL_TYPE, FoldC1);

              _ ->
                CaseC = add_gen_vs(SigT, FoldC1),
                GenV = tv_server:next_name(CaseC#ctx.pid),

                GenTVParamTs = lists:map(fun(_) ->
                  {tv, tv_server:next_name(CaseC#ctx.pid), none, false}
                end, lists:seq(1, IfaceNumParams)),
                GenTV = {gen, GenV, none, NewTV, GenTVParamTs},

                ParamTs = lists:map(fun(_) -> unit end, lists:seq(1, NumParams)),
                GenT = {gen, ImplT, ParamTs},
                add_cst(GenTV, GenT, ImplLoc, ?FROM_IMPL_TYPE, CaseC)
            end,

            {ExprT, FoldC3} = infer(Expr, FoldC2),

            TV = tv_server:fresh(FoldC3#ctx.pid),
            % From doesn't really matter; this cst is always inferred first, so
            % it'll never fail.
            ExprCst = make_cst(
              TV,
              ExprT,
              ?LOC(Expr),
              ?FROM_GLOBAL_DEF(Name),
              FoldC3
            ),
            SigCst = make_cst(
              TV,
              SigT,
              SigLoc,
              ?FROM_GLOBAL_SIG(Name),
              FoldC3
            ),

            % Infer ExprCst first, as inference is in reverse order.
            FoldC4 = append_csts([SigCst, ExprCst], FoldC3),
            FoldC5 = finish_gnr(FoldC4, FoldC#ctx.gnr),
            FoldC5#ctx{env=FoldC#ctx.env}
        end,

        {NewNames, NewC}
    end
  end, {gb_sets:new(), C}, Inits).

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
    % add_dep must be a TV so we can add V to the list of deps when accessed
    {add_dep, {tv, _, _, _}, _} -> true;
    {no_dep, _} -> true
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

% Expensive operation, since it copies all previous csts; use this sparingly.
append_csts(Csts, C) ->
  G = C#ctx.gnr,
  G1 = G#gnr{csts=G#gnr.csts ++ Csts},
  C#ctx{gnr=G1}.

make_cst(T1, T2, Loc, From, C) ->
  {T1, T2, C#ctx.module, Loc, From}.

validate_type(Con, IsIface, NumParams, Loc, C) ->
  case maps:find(Con, C#ctx.types) of
    {ok, {IsIface, NumParams}} -> C;

    {ok, {false, _}} when IsIface ->
      add_ctx_err(?ERR_TYPE_NOT_IFACE(Con), Loc, C);
    {ok, {true, _}} when not IsIface ->
      add_ctx_err(?ERR_IFACE_NOT_TYPE(Con), Loc, C);

    {ok, {_, ExpNumParams}} ->
      Msg = ?ERR_TYPE_PARAMS(Con, ExpNumParams, NumParams),
      add_ctx_err(Msg, Loc, C);

    % TODO: better messages when module is not defined (e.g. Bad.Type) and
    % module is defined but no such type exists (e.g. Module.Bad)
    error when IsIface -> add_ctx_err(?ERR_NOT_DEF_IFACE(Con), Loc, C);
    error when not IsIface -> add_ctx_err(?ERR_NOT_DEF_TYPE(Con), Loc, C)
  end.

validate_iface_field({lam_te, _, ArgTE, ReturnTE}, Name, Loc, C) ->
  case gen_t_num_params(ArgTE) of
    false -> validate_iface_field(ReturnTE, Name, Loc, C);
    _ -> C
  end;
validate_iface_field(_, Name, Loc, C) ->
  add_ctx_err(?ERR_IFACE_TYPE(Name), Loc, C).

add_ctx_err(Msg, Loc, C) ->
  C#ctx{errs=[{Msg, C#ctx.module, Loc} | C#ctx.errs]}.

no_ctx_errs(C1, C2) -> length(C1#ctx.errs) == length(C2#ctx.errs).

add_alias(Con, Vs, T, IsStruct, C) ->
  C#ctx{aliases=(C#ctx.aliases)#{Con => {Vs, T, IsStruct}}}.

norm_sig_type(SigT, RigidVs, Pid) ->
  norm_sig_type(SigT, RigidVs, fvs(SigT), Pid).

norm_sig_type(SigT, RigidVs, FVs, Pid) ->
  RigidVsSet = gb_sets:from_list(RigidVs),

  % TODO: is it more intuitive to change each fv to *fv and then replace?
  Subs = gb_sets:fold(fun(V, FoldSubs) ->
    case gb_sets:is_member(V, RigidVsSet) of
      true -> FoldSubs#{V => {rigid, tv_server:next_name(Pid)}};
      false -> FoldSubs#{V => tv_server:next_name(Pid)}
    end
  end, #{}, FVs),

  % type sigs don't need consolidation, so don't pass aliases
  subs(SigT, #sub_opts{subs=Subs}).

solve(Gs, S) ->
  Map = lists:foldl(fun(G, FoldMap) -> FoldMap#{G#gnr.id => G} end, #{}, Gs),
  %% ?LOG(
  %%   "Generalizations",
  %%   lists:map(fun(G) -> G#gnr{csts=utils:pretty_csts(G#gnr.csts)} end, Gs)
  %% ),

  T = lists:foldl(fun(#gnr{id=ID}, FoldT) ->
    #{ID := #gnr{index=Index}} = FoldT#tarjan.map,
    if
      Index == undefined -> connect(ID, FoldT#tarjan{stack=[]});
      true -> FoldT
    end
  end, #tarjan{map=Map, next_index=0, solver=S}, Gs),

  #solver{
    iv_origins=IVOrigins,
    passed_vs=PassedVs,
    err_vs=ErrVs
  }=S1 = T#tarjan.solver,

  RefVsSet = maps:fold(fun({I, OrigV}, _, FoldRefVsSet) ->
    % Rigid doesn't matter for subs. We specify the iface I so IVs still
    % contains OrigV even if there are no subs.
    SubbedT = subs_s({tv, OrigV, gb_sets:singleton(I), false}, S1),
    IVs = utils:ivs(SubbedT),
    NewVs = gb_sets:from_list(lists:map(fun({_, V}) -> V end, IVs)),
    gb_sets:union(FoldRefVsSet, NewVs)
  end, gb_sets:new(), IVOrigins),

  SubbedErrVs = gb_sets:fold(fun(ErrV, FoldErrVs) ->
    % Is and Rigid don't matter for subs.
    case subs_s({tv, ErrV, none, false}, S1) of
      % If NewV is rigid, it shouldn't be in ErrVs, as it can't be unified with
      % a concrete type.
      {tv, NewV, _, false} -> gb_sets:add(NewV, FoldErrVs);
      _ -> FoldErrVs
    end
  end, gb_sets:new(), ErrVs),

  {_, FinalS} = lists:foldl(fun(PassedV, {FoldReportedVs, FoldS}) ->
    {OrigV, ArgT, Module, Loc, Env} = PassedV,
    % Is and Rigid don't matter for subs.
    SubbedT = subs_s({tv, OrigV, none, false}, FoldS),
    BoundVs = bound_vs(Env, FoldS),

    gb_sets:fold(fun(V, {NestedReportedVs, NestedS}) ->
      IsRefV = gb_sets:is_member(V, RefVsSet),
      IsErrV = gb_sets:is_member(V, SubbedErrVs),
      Bound = gb_sets:is_member(V, BoundVs),
      Reported = gb_sets:is_member(V, NestedReportedVs),

      if
        IsRefV and not IsErrV and not Bound and not Reported ->
          SubbedArgT = subs_s(ArgT, NestedS),
          GenTV = lists:foldl(fun({_, GenTV}, FoldGenTV) ->
            {gen, HiddenV, _, _, _} = GenTV,
            case {HiddenV, FoldGenTV} of
              {V, none} -> GenTV;
              _ -> FoldGenTV
            end
          end, none, gen_vs_list(SubbedArgT)),

          MustSolveT = case GenTV of
            none ->
              {Is, _} = lists:keyfind(V, 2, utils:all_ivs(SubbedArgT)),
              {tv, V, Is, false};
            _ -> GenTV
          end,
          Msg = ?ERR_MUST_SOLVE(
            utils:pretty(MustSolveT),
            utils:pretty(SubbedArgT)
          ),
          NewErrs = [{Msg, Module, Loc} | NestedS#solver.errs],

          NewReportedVs = gb_sets:add(V, NestedReportedVs),
          {NewReportedVs, NestedS#solver{errs=NewErrs}};

        true -> {NestedReportedVs, NestedS}
      end
    end, {FoldReportedVs, FoldS}, fvs(SubbedT))
  end, {gb_sets:new(), S1}, PassedVs),

  case FinalS#solver.errs of
    [] -> {ok, FinalS};

    Errs ->
      Aliases = FinalS#solver.aliases,
      SubbedErrs = lists:map(fun
        ({T1, T2, Module, Loc, From}) ->
          SubbedT1 = subs_s(T1, FinalS, #sub_opts{for_err=true}),
          SubbedT2 = subs_s(T2, FinalS, #sub_opts{for_err=true}),

          IsRecord1 = is_tuple(SubbedT1) andalso (
            element(1, SubbedT1) == record orelse
            element(1, SubbedT1) == record_ext
          ),
          IsRecord2 = is_tuple(SubbedT2) andalso (
            element(1, SubbedT2) == record orelse
            element(1, SubbedT2) == record_ext
          ),

          {FinalT1, FinalT2} = case {IsRecord1, IsRecord2} of
            {true, false} -> {SubbedT1, unalias(SubbedT2, Aliases)};
            {false, true} -> {unalias(SubbedT1, Aliases), SubbedT2};
            _ -> {SubbedT1, SubbedT2}
          end,
          {FinalT1, FinalT2, Module, Loc, From};

        ({_, _, _}=Err) -> Err
      end, Errs),

      {errors, SubbedErrs}
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
      %%     (_, T) -> utils:pretty(T)
      %%   end,
      %%   S3#solver.subs
      %% ),
      %% ?LOG("Subs", PrettySubs),

      S4 = lists:foldl(fun(SolID, FoldS) ->
        #{SolID := SolG} = Map3,
        BoundVs = bound_vs(SolG#gnr.env, FoldS),

        lists:foldl(fun(SolV, NestedS) ->
          SolTV = {tv, SolV, none, false},
          T = subs_s(SolTV, NestedS),
          GVs = gb_sets:subtract(fvs(T), BoundVs),

          #solver{schemes=Schemes} = NestedS,
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
  % deepest expression's constraints first to have better error messages, so we
  % process the list in reverse order here.
  lists:foldr(fun({T1, T2, Module, Loc, From}, FoldS) ->
    {ResolvedT1, FoldS1} = resolve(T1, FoldS),
    {ResolvedT2, FoldS2} = resolve(T2, FoldS1),

    SubbedT1 = subs_s(ResolvedT1, FoldS2),
    SubbedT2 = subs_s(ResolvedT2, FoldS2),
    FoldS3 = FoldS2#solver{
      t1=SubbedT1,
      t2=SubbedT2,
      module=Module,
      loc=Loc,
      from=From
    },

    unify(SubbedT1, SubbedT2, FoldS3)
  end, S#solver{bound_vs=BoundVs, env=Env}, Csts).

resolve({lam, ArgT, ReturnT}, S) ->
  {ResArgT, S1} = resolve(ArgT, S),
  {ResReturnT, S2} = resolve(ReturnT, S1),
  {{lam, ResArgT, ResReturnT}, S2};
resolve({lam, Env, Loc, ArgT, ReturnT}, S) ->
  {ResArgT, S1} = resolve(ArgT, S),
  {ResReturnT, S2} = resolve(ReturnT, S1),
  {{lam, Env, Loc, ResArgT, ResReturnT}, S2};
resolve({tuple, ElemTs}, S) ->
  {ResElemTs, S1} = lists:mapfoldl(fun(T, FoldS) ->
    resolve(T, FoldS)
  end, S, ElemTs),
  {{tuple, ResElemTs}, S1};
resolve({tv, V, Is, Rigid}, S) -> {{tv, V, Is, Rigid}, S};
resolve({con, Con}, S) -> {{con, Con}, S};
resolve({gen, ConT, ParamTs}, S) ->
  {ResConT, S1} = resolve(ConT, S),
  {ResParamTs, S2} = lists:mapfoldl(fun(T, FoldS) ->
    resolve(T, FoldS)
  end, S1, ParamTs),
  {{gen, ResConT, ResParamTs}, S2};
resolve({gen, V, Is, BaseT, ParamTs}, S) ->
  {ResBaseT, S1} = resolve(BaseT, S),
  {{gen, _, ResParamTs}, S2} = resolve({gen, {con, ""}, ParamTs}, S1),
  {{gen, V, Is, ResBaseT, ResParamTs}, S2};
resolve({inst, Ref, {tv, InstV, _, _}=TV}, #solver{inst_refs=InstRefs}=S) ->
  {InstT, NewS} = case maps:find(InstV, S#solver.schemes) of
    error ->
      % We can't compute the final inst T and SubbedVs right now, since we're
      % processing a (mutually) recursive function. Defer the computation until
      % we're done with all unification. Keep a reference to the env to find
      % bound variables.
      %
      % It might seem odd that we're storing the gnr env here, not the ctx env
      % at the point of this inst. This is intentional; if we have a recursive
      % fn bar(x), where X ~ I, and we call bar(x) from within it, we *don't*
      % want x to be in the env. If x is in the env, it'll be consider bound,
      % and no impl will be passed.
      NewInstRefs = InstRefs#{Ref => {deferred, TV, S#solver.env}},
      {TV, S#solver{inst_refs=NewInstRefs}};

    {ok, {_, T}=Scheme} ->
      InstT_ = inst(Scheme, S#solver.pid),
      S1 = case Ref of
        none -> S;
        _ ->
          % Every V of T that can be generalized won't be in InstT_. Only bound,
          % non-generalizable Vs will remain, which shouldn't be in SubbedVs.
          IVs = utils:ivs(InstT_, fvs(T)),
          #solver{iv_origins=IVOrigins} = S,

          case IVs of
            [] -> S;
            _ ->
              SubbedVs = add_subbed_vs(IVs, #{}),
              NewIVOrigins = lists:foldl(fun({Is, V}, FoldIVOrigins) ->
                Origins = gb_sets:singleton({Ref, V}),

                gb_sets:fold(fun(I, NestedIVOrigins) ->
                  NestedIVOrigins#{{I, V} => Origins}
                end, FoldIVOrigins, Is)
              end, IVOrigins, IVs),

              S#solver{
                inst_refs=InstRefs#{Ref => {InstT_, SubbedVs}},
                iv_origins=NewIVOrigins
              }
          end
      end,

      {InstT_, add_gen_vs(InstT_, S1)}
  end,

  resolve(InstT, NewS);
resolve({record, A, FieldMap}, S) ->
  Pairs = maps:to_list(FieldMap),
  {ResPairs, S1} = lists:mapfoldl(fun({Name, T}, FoldS) ->
    {ResT, FoldS1} = resolve(T, FoldS),
    {{Name, ResT}, FoldS1}
  end, S, Pairs),
  {{record, A, maps:from_list(ResPairs)}, S1};
resolve({record_ext, A, BaseT, Ext}, S) ->
  {ResBaseT, S1} = resolve(BaseT, S),
  Pairs = maps:to_list(Ext),

  {ResPairs, S2} = lists:mapfoldl(fun({Name, T}, FoldS) ->
    {ResT, FoldS1} = resolve(T, FoldS),
    {{Name, ResT}, FoldS1}
  end, S1, Pairs),
  {{record_ext, A, ResBaseT, maps:from_list(ResPairs)}, S2};
resolve(unit, S) -> {unit, S}.

inst({GVs, T}, Pid) ->
  Subs = gb_sets:fold(fun(V, FoldSubs) ->
    FoldSubs#{V => tv_server:next_name(Pid)}
  end, #{}, GVs),
  % consolidation already happened when finalizing scheme; no aliases needed
  subs(T, #sub_opts{subs=Subs}).

unify(T1, T2, S) when T1 == T2 -> S;

unify({lam, ArgT1, ReturnT1}, {lam, ArgT2, ReturnT2}, S) ->
  S1 = sub_unify(ArgT1, ArgT2, S),
  case no_errs(S1, S) of
    true -> sub_unify(ReturnT1, ReturnT2, S1);
    false -> S1
  end;
unify({lam, Env, Loc, ArgT1, ReturnT1}, {lam, ArgT2, ReturnT2}, S) ->
  #solver{
    module=Module,
    loc=OrigLoc,
    t1=OrigT1,
    t2=OrigT2,
    passed_vs=PassedVs
  } = S,

  NewPassedVs = gb_sets:fold(fun(V, FoldPassedVs) ->
    [{V, ArgT2, Module, Loc, Env} | FoldPassedVs]
  end, PassedVs, fvs(ArgT2)),

  S1 = S#solver{loc=Loc, t1=ArgT1, t2=ArgT2, passed_vs=NewPassedVs},
  S2 = sub_unify(ArgT1, ArgT2, S1),
  S3 = S2#solver{loc=OrigLoc, t1=OrigT1, t2=OrigT2},

  case {ReturnT1, ReturnT2} of
    % We're continuing to unify arguments passed in a function application.
    % Retain the same t1/t2 as before, so if an error occurs between a lam and
    % a non-lam type, the entire lam types will be included in the error,
    % thereby allowing the reporter to report too many arguments.
    {{lam, _, _, _, _}, _} -> sub_unify(ReturnT1, ReturnT2, S3);

    % We're done with the arguments of the function application. We shouldn't
    % include the full lam types in errors between the return types (not only
    % is it confusing to the user, but it'll also be misconstrued by the
    % reporter as too many arguments), so set the return types to be t1/t2.
    _ -> sub_unify(ReturnT1, ReturnT2, S3#solver{t1=ReturnT1, t2=ReturnT2})
  end;
unify({lam, _, _}=T1, {lam, _, _, _, _}=T2, S) -> sub_unify(T2, T1, S);

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
        false -> S1
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
        false -> S2
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
    false -> S3
  end;

unify({tv, V1, Is1, Rigid1}=TV1, {tv, V2, Is2, Rigid2}=TV2, S) ->
  Bound1 = gb_sets:is_member(V1, S#solver.bound_vs),
  Bound2 = gb_sets:is_member(V2, S#solver.bound_vs),
  Occurs = occurs(V1, TV2) or occurs(V2, TV1),

  if
    Occurs -> add_err(S);

    not Rigid1, not Bound1, Rigid2 ->
      IsSubset = Is1 == none orelse
        (Is2 /= none andalso gb_sets:is_subset(Is1, Is2)),
      if
        IsSubset -> add_sub(V1, TV2, S);
        true -> add_err(S)
      end;

    not Rigid2, not Bound2, Rigid1 ->
      IsSubset = Is2 == none orelse
        (Is1 /= none andalso gb_sets:is_subset(Is2, Is1)),
      if
        IsSubset -> add_sub(V2, TV1, S);
        true -> add_err(S)
      end;

    not Rigid1, not Rigid2 ->
      GenVs = S#solver.gen_vs,
      NewGenVs = case {maps:find(V1, GenVs), maps:find(V2, GenVs)} of
        {error, error} -> GenVs;
        {{ok, GenTVs}, error} -> GenVs#{V2 => GenTVs};
        {error, {ok, GenTVs}} -> GenVs#{V1 => GenTVs};
        {{ok, GenTVs1}, {ok, GenTVs2}} ->
          MergedGenTVs = GenTVs1 ++ GenTVs2,
          GenVs#{V1 => MergedGenTVs, V2 => MergedGenTVs}
      end,
      S1 = S#solver{gen_vs=NewGenVs},

      if
        Is1 == none -> add_sub(V1, TV2, S1);
        Is2 == none -> add_sub(V2, TV1, S1);
        true ->
          MergedIs = {set_ifaces, gb_sets:union(Is1, Is2)},
          S2 = add_sub(V1, MergedIs, add_sub(V2, TV1, S1)),
          merge_iv_origins(Is2, V2, V1, S2)
      end;

    true -> add_err(S)
  end;

unify({tv, V, Is, Rigid}, T, S) ->
  Occurs = occurs(V, T),
  Bound = gb_sets:is_member(V, S#solver.bound_vs),
  WouldEscape = Bound and occurs(true, T),

  if
    % Don't add V to ErrVs here because it can't actually be unified with
    % a concrete type.
    Rigid -> add_err(S);

    Occurs or WouldEscape -> add_err_v(V, add_err(S));
    true ->
      S1 = case {T, Is} of
        % V can sub with anything, so just sub V with GenTV below
        {_, none} -> S;

        % same interfaces, so just sub V with GenTV below
        {{gen, _, Is, _, _}, _} -> S;

        % different interfaces and GenTV is rigid, so fail
        {{gen, _, _, {tv, _, _, true}, _}, _} -> add_err(S);

        % different interfaces and GenTV isn't rigid
        {{gen, V1, Is1, _, _}, _} ->
          % We need the gen TV to adopt the interfaces of V, and V to be
          % replaced with the gen TV. The former is done here, and the latter
          % is done further below.
          %
          % If the GenTV has a BaseT that is a TV, we don't need to do anything
          % further. If the GenTV has a BaseT that is not a TV, then there was
          % previously an attempt at unification that failed, and we avoid
          % propagating errors by doing nothing else here.
          MergedIs = case {Is, Is1} of
            {_, none} -> Is;
            {none, _} -> Is1;
            _ -> gb_sets:union(Is, Is1)
          end,
          CaseS = add_sub(V1, {set_ifaces, MergedIs}, S),
          merge_iv_origins(Is, V, V1, CaseS);

        _ -> gb_sets:fold(fun(I, FoldS) -> instance(T, I, V, FoldS) end, S, Is)
      end,

      case no_errs(S1, S) of
        true -> add_sub(V, T, S1);
        false -> add_err_v(V, S1)
      end
  end;
unify(T, {tv, V, Is, Rigid}, S) -> sub_unify({tv, V, Is, Rigid}, T, S);

unify({gen, {con, Con}, ParamTs1}, {gen, {con, Con}, ParamTs2}, S) ->
  if
    length(ParamTs1) /= length(ParamTs2) -> add_err(S);
    true ->
      lists:foldl(fun({T1, T2}, FoldS) ->
        sub_unify(T1, T2, FoldS)
      end, S, lists:zip(ParamTs1, ParamTs2))
  end;

% If BaseT is *not* a TV, then this gen TV should've been replaced with
% a regular gen. It hasn't been replaced due to a unification error. Avoid
% propagating errors.
unify({gen, _, _, BaseT, _}, _, S) when element(1, BaseT) /= tv -> S;
unify(_, {gen, _, _, BaseT, _}, S) when element(1, BaseT) /= tv -> S;

unify({gen, ConT, ParamTs1}=GenT, {gen, V, Is, BaseTV, ParamTs2}=GenTV, S) ->
  S1 = if
    length(ParamTs1) == length(ParamTs2) ->
      lists:foldl(fun({T1, T2}, FoldS) ->
        sub_unify(T1, T2, FoldS)
      end, S, lists:zip(ParamTs1, ParamTs2));

    true ->
      case ParamTs2 of
        [{tv, _, _, _}] -> S;
        [{tuple, Elems}] when length(Elems) == length(ParamTs1) -> S;
        _ -> add_err(S)
      end
  end,

  case no_errs(S1, S) of
    false -> S1;
    true ->
      S2 = sub_unify(BaseTV, ConT, S1),
      case no_errs(S2, S1) of
        false -> S2;
        true ->
          S3 = sub_unify_gen_vs(GenTV, ConT, length(ParamTs1), S2),
          case no_errs(S3, S2) of
            false -> S3;
            true -> sub_unify({tv, V, Is, false}, GenT, S3)
          end
      end
  end;
unify({gen, _, _, _, _}=T1, {gen, _, _}=T2, S) -> sub_unify(T2, T1, S);

unify(
  {gen, V1, Is1, BaseTV1, ParamTs1}=GenTV1,
  {gen, V2, Is2, BaseTV2, ParamTs2}=GenTV2,
  S
) ->
  Length1 = length(ParamTs1),
  Length2 = length(ParamTs2),
  SameLengths = Length1 == Length2,

  S1 = if
    SameLengths ->
      lists:foldl(fun({T1, T2}, FoldS) ->
        sub_unify(T1, T2, FoldS)
      end, S, lists:zip(ParamTs1, ParamTs2));

    Length1 == 1 ->
      case ParamTs1 of
        [{tv, _, _, _}] -> S;
        [{tuple, Elems}] when length(Elems) == length(ParamTs2) -> S;
        _ -> add_err(S)
      end;

    Length2 == 1 ->
      case ParamTs2 of
        [{tv, _, _, _}] -> S;
        [{tuple, Elems}] when length(Elems) == length(ParamTs1) -> S;
        _ -> add_err(S)
      end;

    true -> add_err(S)
  end,

  case no_errs(S1, S) of
    false -> S1;
    true ->
      % Do this before unifying BaseTV1 and BaseTV2 so the GenTV sets are
      % merged after params are fixed.
      S2 = if
        not SameLengths andalso Length1 == 1 ->
          sub_unify_gen_vs(GenTV1, none, Length2, S1);
        not SameLengths andalso Length2 == 1 ->
          sub_unify_gen_vs(GenTV2, none, Length1, S1);
        true -> S1
      end,

      case no_errs(S2, S1) of
        false -> S2;
        true ->
          S3 = sub_unify(BaseTV1, BaseTV2, S2),
          case no_errs(S3, S2) of
            false -> S3;
            true -> sub_unify({tv, V1, Is1, false}, {tv, V2, Is2, false}, S3)
          end
      end
  end;

unify(T1, T2, S) when element(1, T2) == record; element(1, T2) == record_ext ->
  case unalias(T1, S#solver.aliases) of
    T1 -> add_err(S);
    NewT1 ->
      S1 = sub_unify(NewT1, T2, S),
      A = element(2, T2),
      NoErrs = no_errs(S, S1),
      if
        NoErrs andalso A /= none -> add_sub(A, T1, S1);
        true -> S1
      end
  end;
unify(T1, T2, S) when element(1, T1) == record; element(1, T1) == record_ext ->
  sub_unify(T2, T1, S);

unify(T1, T2, S) ->
  case {unalias(T1, S#solver.aliases), unalias(T2, S#solver.aliases)} of
    {T1, T2} -> add_err(S);
    % at least one type was an alias
    {NewT1, NewT2} -> sub_unify(NewT1, NewT2, S)
  end.

sub_unify(T1, T2, S) -> unify(subs_s(T1, S), subs_s(T2, S), S).

sub_unify_gen_vs(
  {gen, _, _, {tv, BaseV, _, _}, ParamTs},
  ConT,
  NewNumParams,
  #solver{t1=OrigT1, t2=OrigT2}=S
) ->
  NumParams = length(ParamTs),
  GenVs = maps:get(BaseV, S#solver.gen_vs),

  S1 = lists:foldl(fun(GenTV, FoldS) ->
    {gen, FoldV, FoldIs, FoldBaseTV, FoldParamTs} = GenTV,
    NewParamTs = if
      NumParams /= NewNumParams ->
        lists:map(fun(_) ->
          tv_server:fresh(FoldS#solver.pid)
        end, lists:seq(1, NewNumParams));

      true -> none
    end,

    TargetT = if
      ConT /= none andalso NewParamTs /= none -> {gen, ConT, NewParamTs};
      ConT /= none -> {gen, ConT, FoldParamTs};
      NewParamTs /= none ->
        NewV = tv_server:next_name(FoldS#solver.pid),
        {gen, NewV, FoldIs, FoldBaseTV, NewParamTs}
    end,

    FoldS1 = FoldS#solver{t1=GenTV, t2=TargetT},
    FoldS2 = case NewParamTs of
      none -> FoldS1;
      _ ->
        [FoldParamT] = FoldParamTs,
        sub_unify(FoldParamT, {tuple, NewParamTs}, FoldS1)
    end,

    case no_errs(FoldS2, FoldS1) of
      false -> FoldS2;
      true -> sub_unify({tv, FoldV, FoldIs, false}, TargetT, FoldS2)
    end
  end, S, GenVs),

  S1#solver{t1=OrigT1, t2=OrigT2}.

merge_iv_origins(Is, V, TargetV, S) ->
  IsExceptBuiltin = gb_sets:difference(Is, utils:builtin_is()),
  NewIVOrigins = gb_sets:fold(fun(I, FoldIVOrigins) ->
    VOrigins = maps:get({I, V}, FoldIVOrigins),
    case maps:find({I, TargetV}, FoldIVOrigins) of
      {ok, TargetVOrigins} ->
        MergedOrigins = gb_sets:union(VOrigins, TargetVOrigins),
        FoldIVOrigins#{{I, TargetV} => MergedOrigins};
      error -> FoldIVOrigins#{{I, TargetV} => VOrigins}
    end
  end, S#solver.iv_origins, IsExceptBuiltin),
  S#solver{iv_origins=NewIVOrigins}.

add_sub(V, RawSub, S) ->
  Sub = case RawSub of
    % We don't want to keep the locations of arguments if we're subbing for
    % a function application. This aids comprehension: we can only ever
    % unify a function application (a 4-tuple lam) with a regular 3-tuple lam.
    {lam, _, _, _, _} -> remove_app_meta(RawSub);
    _ -> RawSub
  end,

  S1 = case maps:find(V, S#solver.subs) of
    error -> S#solver{subs=(S#solver.subs)#{V => Sub}};
    % we're allowed to override set_ifaces to another value
    {ok, {set_ifaces, _}} -> S#solver{subs=(S#solver.subs)#{V => Sub}};
    {ok, Existing} -> error({badarg, V, Existing, Sub})
  end,

  BoundVs = S1#solver.bound_vs,
  case {Sub, gb_sets:is_member(V, BoundVs)} of
    % no change in fvs
    {{set_ifaces, _}, _} -> S1;
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

add_err_v(V, #solver{err_vs=ErrVs}=S) ->
  S#solver{err_vs=gb_sets:add(V, ErrVs)}.

no_errs(S1, S2) -> length(S1#solver.errs) == length(S2#solver.errs).

unalias({con, Con}, Aliases) ->
  case maps:find(Con, Aliases) of
    {ok, {[], T, _}} -> unalias(T, Aliases);
    error -> {con, Con}
  end;
unalias({gen, {con, Con}, ParamTs}, Aliases) ->
  case maps:find(Con, Aliases) of
    {ok, {Vs, T, _}} ->
      Subs = maps:from_list(lists:zip(Vs, ParamTs)),
      unalias(subs(T, #sub_opts{subs=Subs, aliases=Aliases}), Aliases);
    % no need to unalias ParamTs because we'll sub_unify them
    error -> {gen, {con, Con}, ParamTs}
  end;
unalias(T, _) -> T.

unalias_except_struct({con, Con}, Aliases) ->
  case maps:find(Con, Aliases) of
    {ok, {[], T, false}} -> unalias_except_struct(T, Aliases);
    _ -> {con, Con}
  end;
unalias_except_struct({gen, {con, Con}, ParamTs}, Aliases) ->
  case maps:find(Con, Aliases) of
    {ok, {Vs, T, false}} ->
      Subs = maps:from_list(lists:zip(Vs, ParamTs)),
      Opts = #sub_opts{subs=Subs, aliases=Aliases},
      unalias_except_struct(subs(T, Opts), Aliases);
    % no need to unalias ParamTs because we'll recursively unalias them if
    % necessary in infer_sig_helper
    _ -> {gen, {con, Con}, ParamTs}
  end;
unalias_except_struct(T, _) -> T.

instance({con, "Int"}, "Num", _, S) -> S;
instance({con, "Float"}, "Num", _, S) -> S;
instance({con, "String"}, "Concatable", _, S) -> S;
instance({gen, {con, "List"}, _}, "Concatable", _, S) -> S;
instance({gen, {con, "Map"}, _}, "Concatable", _, S) -> S;
instance({gen, {con, "Set"}, _}, "Concatable", _, S) -> S;
instance({gen, {con, "List"}, _}, "Separable", _, S) -> S;
instance({gen, {con, "Set"}, _}, "Separable", _, S) -> S;
instance(T, I, V, S) ->
  Key = utils:impl_key(T),
  case maps:find(Key, maps:get(I, S#solver.impls)) of
    {ok, {RawT, _, _, _}} ->
      NormT = norm_sig_type(RawT, [], S#solver.pid),
      IVs = utils:ivs(NormT),

      S1 = case IVs of
        [] -> S;
        _ ->
          #solver{
            inst_refs=InstRefs,
            iv_origins=IVOrigins,
            nested_ivs=NestedIVs
          } = S,

          % TODO: is there a case where this fails?
          Origins = maps:get({I, V}, IVOrigins),

          {NewInstRefs, NewNestedIVs} = gb_sets:fold(fun({Ref, OrigV}, Memo) ->
            {FoldInstRefs, FoldNestedIVs} = Memo,
            {InstT, SubbedVs} = maps:get(Ref, FoldInstRefs),
            SubbedVs1 = add_subbed_vs(IVs, SubbedVs),

            FoldInstRefs1 = FoldInstRefs#{Ref => {InstT, SubbedVs1}},
            FoldNestedIVs1 = FoldNestedIVs#{{I, OrigV} => IVs},
            {FoldInstRefs1, FoldNestedIVs1}
          end, {InstRefs, NestedIVs}, Origins),

          NewIVOrigins = lists:foldl(fun({NestedIs, NestedV}, FoldIVOrigins) ->
            NestedOrigins = gb_sets:fold(fun({Ref, _}, FoldOrigins) ->
              gb_sets:add({Ref, NestedV}, FoldOrigins)
            end, gb_sets:new(), Origins),

            gb_sets:fold(fun(NestedI, NestedIVOrigins) ->
              NestedIVOrigins#{{NestedI, NestedV} => NestedOrigins}
            end, FoldIVOrigins, NestedIs)
          end, IVOrigins, IVs),

          S#solver{
            inst_refs=NewInstRefs,
            iv_origins=NewIVOrigins,
            nested_ivs=NewNestedIVs
          }
      end,

      sub_unify(T, NormT, S1);

    error -> add_err(S)
  end.

add_subbed_vs(IVs, SubbedVs) ->
  lists:foldl(fun({Is, V}, FoldSubbedVs) ->
    % Rigid doesn't matter here, but note that these Vs are non-rigid
    % anyway because they're instantiated.
    FoldSubbedVs#{V => {tv, V, Is, false}}
  end, SubbedVs, IVs).

remove_app_meta({lam, _, _, ArgT, ReturnT}) ->
  {lam, ArgT, remove_app_meta(ReturnT)};
remove_app_meta(T) -> T.

subs_s(T, S) -> subs_s(T, S, #sub_opts{}).

subs_s(T, #solver{subs=Subs, aliases=Aliases}, Opts) ->
  subs(T, Opts#sub_opts{subs=Subs, aliases=Aliases}).

subs({lam, ArgT, ReturnT}, Opts) ->
  {lam, subs(ArgT, Opts), subs(ReturnT, Opts)};
subs({lam, Env, Loc, ArgT, ReturnT}, Opts) ->
  {lam, Env, Loc, subs(ArgT, Opts), subs(ReturnT, Opts)};
subs({tuple, ElemTs}, Opts) ->
  {tuple, lists:map(fun(T) -> subs(T, Opts) end, ElemTs)};
subs({tv, V, Is, Rigid}=TV, #sub_opts{subs=Subs}=Opts) ->
  case maps:find(V, Subs) of
    error -> TV;
    {ok, {rigid, V1}} -> {tv, V1, Is, true};

    {ok, {set_ifaces, NewIs}} ->
      false = Rigid,
      {tv, V, NewIs, Rigid};

    {ok, Value} ->
      Sub = if
        % Instantiation, so rigid resets to false
        is_list(Value) -> {tv, Value, Is, false};
        % Replacing with a new type entirely
        true -> Value
      end,
      subs(Sub, Opts)
  end;
subs({con, Con}, _) -> {con, Con};
subs({gen, ConT, ParamTs}, Opts) ->
  {gen, subs(ConT, Opts), lists:map(fun(T) -> subs(T, Opts) end, ParamTs)};
subs({gen, V, Is, BaseT, ParamTs}, #sub_opts{for_err=ForErr}=Opts) ->
  case subs({tv, V, Is, false}, Opts) of
    {tv, NewV, NewIs, _} ->
      % When reporting errors, do *not* sub BaseT; if BaseT is subbed and
      % V isn't subbed, that indicates a unification error with a regular gen.
      % We avoid subbing BaseT for better error messages; instead of
      % mismatched List<A> ~ Num and [A], we get T<A> ~ Num and [A].
      SubbedBaseT = if
        ForErr -> BaseT;
        true -> subs(BaseT, Opts)
      end,
      {gen, _, SubbedParamTs} = subs({gen, {con, ""}, ParamTs}, Opts),
      {gen, NewV, NewIs, SubbedBaseT, SubbedParamTs};

    SubbedT -> subs(SubbedT, Opts)
  end;
subs({record, A, FieldMap}, #sub_opts{subs=Subs}=Opts) ->
  case maps:find(A, Subs) of
    error -> {record, A, maps:map(fun(_, T) -> subs(T, Opts) end, FieldMap)};
    {ok, {anchor, NewA}} -> subs({record, NewA, FieldMap}, Opts);
    {ok, T} -> subs(T, Opts)
  end;
subs({record_ext, A, BaseT, Ext}, #sub_opts{subs=Subs, aliases=Aliases}=Opts) ->
  case maps:find(A, Subs) of
    error ->
      NewExt = maps:map(fun(_, T) -> subs(T, Opts) end, Ext),
      consolidate({record_ext, A, subs(BaseT, Opts), NewExt}, Aliases);
    {ok, {anchor, NewA}} ->
      subs({record_ext, NewA, BaseT, Ext}, Opts);
    {ok, T} -> subs(T, Opts)
  end;
subs(unit, _) -> unit.

consolidate({record_ext, A, {record_ext, _, BaseT, Ext1}, Ext2}, Aliases) ->
  consolidate({record_ext, A, BaseT, maps:merge(Ext1, Ext2)}, Aliases);
consolidate({record_ext, A, {record, _, FieldMap}, Ext}, _) ->
  {record, A, maps:merge(FieldMap, Ext)};
consolidate({record_ext, A, BaseT, Ext}, Aliases) ->
  case unalias(BaseT, Aliases) of
    % invalid base; just return as is
    BaseT -> {record_ext, A, BaseT, Ext};
    NewBaseT -> consolidate({record_ext, A, NewBaseT, Ext}, Aliases)
  end.

bound_vs(Env, #solver{schemes=Schemes}=S) ->
  maps:fold(fun(_, {Value, _}, FoldVs) ->
    case Value of
      {no_dep, T} -> gb_sets:union(FoldVs, fvs(subs_s(T, S)));

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
fvs({lam, _, _, ArgT, ReturnT}) -> fvs({lam, ArgT, ReturnT});
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
fvs({gen, V, _, BaseT, ParamTs}) ->
  % V only exists to track ifaces associated with this gen TV; it isn't a
  % regular type variable. That being said, it still must be included in FVs.
  % We assume FVs is a superset of IVs, and often use FVs to determine IVs;
  % V is an IV, and hence it must be incldued in FVs.
  gb_sets:add(V, gb_sets:union(fvs(BaseT), fvs({gen, {con, ""}, ParamTs})));
% fvs({inst, ...}) ommitted; they should be resolved
fvs({record, _, FieldMap}) ->
  maps:fold(fun(_, T, S) ->
    gb_sets:union(S, fvs(T))
  end, gb_sets:new(), FieldMap);
fvs({record_ext, _, BaseT, Ext}) ->
  gb_sets:union(fvs(BaseT), fvs({record, none, Ext}));
fvs(unit) -> gb_sets:new().

add_gen_vs(InstT, Record) ->
  GenVsList = gen_vs_list(InstT),
  GenVs = case element(1, Record) of
    ctx -> Record#ctx.gen_vs;
    solver -> Record#solver.gen_vs
  end,

  NewGenVs = lists:foldl(fun({V, GenTV}, FoldGenVs) ->
    case maps:find(V, FoldGenVs) of
      error -> FoldGenVs#{V => [GenTV]};
      {ok, GenTVs} -> FoldGenVs#{V => [GenTV | GenTVs]}
    end
  end, GenVs, GenVsList),

  case element(1, Record) of
    ctx -> Record#ctx{gen_vs=NewGenVs};
    solver -> Record#solver{gen_vs=NewGenVs}
  end.

gen_vs_list({lam, ArgT, ReturnT}) -> gen_vs_list(ArgT) ++ gen_vs_list(ReturnT);
gen_vs_list({lam, _, _, ArgT, ReturnT}) -> gen_vs_list({lam, ArgT, ReturnT});
gen_vs_list({tuple, ElemTs}) -> lists:flatmap(fun gen_vs_list/1, ElemTs);
gen_vs_list({tv, _, _, _}) -> [];
gen_vs_list({con, _}) -> [];
gen_vs_list({gen, _, ParamTs}) -> lists:flatmap(fun gen_vs_list/1, ParamTs);
gen_vs_list({gen, _, _, {tv, V, _, _}, ParamTs}=GenTV) ->
  [{V, GenTV} | gen_vs_list({gen, {con, ""}, ParamTs})];
% gen_vs_list({inst, ...}) ommitted; they should be resolved
gen_vs_list({record, _, FieldMap}) ->
  lists:flatmap(fun(Key) ->
    gen_vs_list(maps:get(Key, FieldMap))
  end, maps:keys(FieldMap));
gen_vs_list({record_ext, _, BaseT, Ext}) ->
  gen_vs_list(BaseT) ++ gen_vs_list({record, none, Ext});
gen_vs_list(unit) -> [].

occurs(V, {lam, ArgT, ReturnT}) ->
  occurs(V, ArgT) orelse occurs(V, ReturnT);
occurs(V, {lam, _, _, ArgT, ReturnT}) -> occurs(V, {lam, ArgT, ReturnT});
occurs(V, {tuple, ElemTs}) ->
  lists:foldl(fun(T, Occurs) ->
    Occurs orelse occurs(V, T)
  end, false, ElemTs);
occurs(V, {tv, V1, _, Rigid}) -> (V == Rigid) orelse (V == V1);
occurs(_, {con, _}) -> false;
occurs(V, {gen, _, ParamTs}) ->
  lists:foldl(fun(T, Occurs) ->
    Occurs orelse occurs(V, T)
  end, false, ParamTs);
occurs(V, {gen, V1, _, BaseT, ParamTs}) ->
  (V == V1) orelse occurs(V, BaseT) orelse occurs(V, {gen, {con, ""}, ParamTs});
% occurs({inst, ...}) ommitted; they should be resolved
occurs(V, {record, _, FieldMap}) ->
  maps:fold(fun(_, T, Occurs) ->
    Occurs or occurs(V, T)
  end, false, FieldMap);
occurs(V, {record_ext, _, BaseT, Ext}) ->
  occurs(V, BaseT) orelse occurs(V, {record, none, Ext});
occurs(_, unit) -> false.
