-module(type_system).
-export([
  infer_file/1,
  infer_prg/1,
  pattern_names/1,
  parse_file/2,
  rigid_err/4
]).
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
%   {lam, [ArgTs], ReturnT} - a lambda type (ArgT1, ArgT2, ...) -> ReturnT;
%     e.g. (Int, String) -> Bool
%   TV - see explanation above
%
% fresh - a function that generates a new TV.
% fvs - a function that computes the set of free TV names in an expression.
% Scheme - a tuple {GVs, T, BoundVs} that represents a T generalized across GVs,
%   a set of TV names. BoundVs are the bound Vs in T.

% S - a solver record used to unify types and solve constraints
%   subs - the substitutions made to unify types
%   errs - any constraints that couldn't be unified
%   schemes - the schemes of env variables that have been solved for and
%     generalized
%   bound_vs - the set of TV names in the environment
%   inst_refs - a Ref => {T, SubbedVs} mapping of instantiated variables
%   iv_origins - a {I, V} => Origins mapping for Vs coming from inst vars
%   aliases - see aliases in ctx record
%   ifaces - a Name => {Fields, FieldTs} map for interfaces in the env
%   impls - a I => {RawT, InstT, Inits} mapping of impls
%   nested_ivs - a {I, V} => IVs mapping for impls depending on other impls
%   passed_vs - a V => {Is, ArgT, Module, Loc} mapping of Vs that have args
%     passed in for them
%   return_vs - a V => {Is, ReturnT, Module, Loc} mapping for IVs in return
%     types that are fully applied
%   must_solve_vs - a set of Vs that must be solved because of their interface
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
  record_refs = #{},
  iv_origins = #{},
  aliases,
  ifaces,
  impls,
  nested_ivs = #{},
  passed_vs = [],
  return_vs = [],
  must_solve_vs = ordsets:new(),
  err_vs = ordsets:new(),
  gen_vs,
  t1,
  t2,
  module,
  loc,
  from,
  l_env,
  pid
}).

% G - a gnr record that represents a set of constraints to solve before
%     generalizing a type variable:
%   v - the TV name to generalize
%   env - a Name => T mapping of bindings in the environment
%   csts - an array of constraints to solve before generalizing
%   deps - a set of TV names corresponding to gnr records that need to solved
%     before this record or, in the case of (mutual) recursion,
%     simultaneously with this record
%   index / low_link / on_stack - bookkeeping for Tarjan's strongly connected
%     components algorithm; see T below and [1]
-record(gnr, {
  id,
  vs,
  l_env,
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

-ifdef(TEST).
  -define(
    LOG(Prefix, Value),
    io:format("~n(~p:~p) ~s:~n~p~n", [?MODULE, ?LINE, Prefix, Value])
  ).
-else.
  -define(LOG(Prefix, Value), true).
-endif.

% this also initializes the lexer by dependency
load() -> par_native:init('Parser').

infer_file(Path) ->
  case parse_file(Path, #{}) of
    {ok, _, Comps, _} -> infer_comps(Comps);
    {errors, Errors, _} -> Errors
  end.

stdlib_dir() -> filename:join(code:lib_dir(par, src), "lib").

stdlib_modules() ->
  #{
    "Base" => "base.par",
    "List" => "list.par",
    "Set" => "set.par",
    "Map" => "map.par",
    "String" => "string.par",
    "Char" => "char.par",
    "Test" => "test.par"
  }.

resolve_dep_path(RawPath) ->
  case filename:extension(RawPath) of
    "" -> utils:absolute(RawPath ++ ".par");
    _ -> utils:absolute(RawPath)
  end.

parse_file(RawPath, Parsed) ->
  Path = resolve_dep_path(RawPath),

  case maps:find(Path, Parsed) of
    {ok, {module, Module}} -> {ok, Module, [], Parsed};
    {ok, skip} -> skip;

    error ->
      StdlibDir = stdlib_dir(),
      IsStdlib = lists:prefix(StdlibDir, Path),

      Result = case IsStdlib of
        true ->
          case erl_prim_loader:get_file(Path) of
            {ok, Bin, _} -> {ok, Bin};
            error -> {error, "builtin module of that name doesn't exist"}
          end;
        false -> file:read_file(Path)
      end,

      case Result of
        {error, Reason} ->
          {errors, [{read_error, Path, Reason}], Parsed#{Path => skip}};

        {ok, Binary} ->
          Prg = utils:codepoints(Binary),

          case parse_prg(Prg, Path) of
            {ok, RawAst, PrgLines} ->
              Ast = case IsStdlib of
                true -> RawAst;
                false -> add_stdlib_imports(RawAst)
              end,

              {module, _, {con_token, _, Module}, Imports, _} = Ast,
              Parsed1 = Parsed#{Path => {module, Module}},

              Comp = #comp{
                module=Module,
                ast=Ast,
                path=Path,
                prg=Prg,
                prg_lines=PrgLines
              },
              Dir = filename:dirname(Path),

              {Deps, Comps, AllErrors, Parsed2} = lists:foldr(fun(Import, Memo) ->
                {import, _, From, Idents} = Import,
                {FoldDeps, FoldComps, FoldAllErrors, FoldParsed} = Memo,

                {DepLoc, DepPath} = case From of
                  {str, DepLoc_, DepPath_} ->
                    {DepLoc_, filename:join(Dir, utils:codepoints(DepPath_))};
                  {con_token, DepLoc_, StdlibModule} ->
                    case maps:find(StdlibModule, stdlib_modules()) of
                      {ok, DepPath_} ->
                        {DepLoc_, filename:join(StdlibDir, DepPath_)};

                      % The file null doesn't exist and will cause a read error
                      % below, which will translate to an import error.
                      error -> {DepLoc_, filename:join(StdlibDir, null)}
                    end
                end,

                case resolve_dep_path(DepPath) of
                  Path ->
                    Msg = "this is a recursive self import",
                    Err = {import_error, DepLoc, Path, Msg, Comp},
                    {FoldDeps, FoldComps, [[Err] | FoldAllErrors], FoldParsed};

                  _ ->
                    case parse_file(DepPath, FoldParsed) of
                      {ok, DepModule, DepComps, NewParsed} ->
                        {[{DepModule, Idents} | FoldDeps],
                          [DepComps | FoldComps], FoldAllErrors, NewParsed};

                      {errors, [{read_error, ImportPath, Reason}], NewParsed} ->
                        ImportPathOrModule = case From of
                          {str, _, _} -> ImportPath;
                          {con_token, _, ImportModule} -> ImportModule
                        end,
                        Err = {import_error, DepLoc, ImportPathOrModule,
                          Reason, Comp},
                        {FoldDeps, FoldComps, [[Err] | FoldAllErrors],
                          NewParsed};

                      {errors, DepAllErrors, NewParsed} ->
                        {FoldDeps, FoldComps, [DepAllErrors | FoldAllErrors],
                          NewParsed};

                      skip -> Memo
                    end
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

add_stdlib_imports({module, _, _, RawImports, _}=Ast) ->
  Imported = lists:filtermap(fun
    ({import, _, {con_token, _, Con}, _}) -> {true, Con};
    (_) -> false
  end, RawImports),
  ImportedSet = ordsets:from_list(Imported),

  RawStdlibImports = lists:map(fun(Name) ->
    Idents = case Name of
      "Base" -> [{all, ?BUILTIN_LOC}];
      _ -> []
    end,
    {import, ?BUILTIN_LOC, {con_token, ?BUILTIN_LOC, Name}, Idents}
  end, maps:keys(stdlib_modules())),
  StdlibImports = lists:filter(fun({import, _, {con_token, _, Con}, _}) ->
    not ordsets:is_element(Con, ImportedSet)
  end, RawStdlibImports),

  setelement(4, Ast, StdlibImports ++ RawImports).

infer_prg(Prg) ->
  case parse_prg(Prg, "[infer-prg]") of
    {ok, Ast, PrgLines} ->
      % infer_prg should only be used only when there are no imports
      {module, _, {con_token, _, Module}, Imports, _} = Ast,
      case Imports of
        [] -> ok;
        _ -> error("infer_prg expects no imports")
      end,
      %% ?LOG("Ast", Ast),

      Comp = #comp{
        module=Module,
        ast=Ast,
        deps=[],
        path="[infer-prg]",
        prg=Prg,
        prg_lines=PrgLines
      },
      infer_comps([Comp]);

    Errors -> Errors
  end.

parse_prg(Prg, Path) ->
  PrgLines = array:from_list(re:split(Prg, "\r?\n", [{return, list}])),
  case 'Lexer':tokenize(Prg) of
    {errors, Errs} -> {lexer_errors, Errs, Path, PrgLines};
    {ok, Tokens} ->
      %% io:format(user, "map ~p~n\n", [code:is_loaded('Map')]),
      case 'Parser':parse(Tokens) of
        #{errs := [_ | _]=Errs} -> {parser_errors, Errs, Path, PrgLines};
        #{value := {'Some', Ast}} -> {ok, Ast, PrgLines}
      end
  end.

infer_comps(RawComps) ->
  {ok, Pid} = tv_server:start_link(),

  {Comps, _, C} = lists:foldr(fun(Comp, {FoldComps, Modules, FoldC}) ->
    #comp{module=Module, ast={module, _, {con_token, Loc, _}, _, _}} = Comp,
    FoldC1 = FoldC#ctx{module=Module},

    case ordsets:is_element(Module, Modules) of
      true ->
        FoldC2 = add_ctx_err(?ERR_REDEF_MODULE(Module), Loc, FoldC1),
        {FoldComps, Modules, FoldC2};
      false ->
        Exports = FoldC1#ctx.exports,
        NewExports = Exports#{Module => ordsets:new()},
        NewModules = ordsets:add_element(Module, Modules),
        {[Comp | FoldComps], NewModules, FoldC1#ctx{exports=NewExports}}
    end
  end, {[], ordsets:new(), #ctx{pid=Pid}}, RawComps),

  C1 = populate_env_and_types(Comps, C),
  C2 = infer_defs(Comps, C1),
  S = #solver{
    errs=C2#ctx.errs,
    aliases=C2#ctx.aliases,
    ifaces=C2#ctx.ifaces,
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

      FinalGEnv = maps:map(fun(_, #binding{tv={tv, V, _, _}}=B) ->
        {GVs, T, _} = maps:get(V, Schemes),
        B#binding{inst=inst(GVs, T, Pid)}
      end, C2#ctx.g_env),

      SubbedInstRefsPairs = lists:filtermap(fun
        % In the case of a (mutually) recursive function, we defer computing the
        % SubbedVs until now, as we couldn't inst it earlier.
        ({Ref, {deferred, TV, LEnv}}) ->
          T = subs_s(TV, FinalS),
          BoundVs = bound_vs(LEnv, FinalS),
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

      SubbedFnRefs = maps:map(fun(_, {T, LEnv}) ->
        BoundVs = bound_vs(LEnv, FinalS),
        utils:args_ivs(subs_s(T, FinalS), BoundVs)
      end, C2#ctx.fn_refs),

      SubbedRecordRefs = maps:map(fun(_, T) ->
        subs_s(T, FinalS)
      end, C2#ctx.record_refs),

      FinalC = C2#ctx{
        g_env=FinalGEnv,
        inst_refs=SubbedInstRefs,
        fn_refs=SubbedFnRefs,
        nested_ivs=NestedIVs,
        record_refs=SubbedRecordRefs
      },
      {ok, Comps, FinalC};

    {errors, Errs} -> {errors, Errs, Comps}
  end,

  ok = tv_server:stop(Pid),
  Result.

populate_env_and_types(Comps, C) ->
  lists:foldl(fun(Comp, FoldC) ->
    #comp{module=Module, ast={module, _, _, _, Defs}} = Comp,

    lists:foldl(fun(Node, ModuleC) ->
      case Node of
        {global, _, {var, Loc, Name}, _, Exported} ->
          {TV, ID} = tv_server:fresh_gnr_id(ModuleC#ctx.pid),
          B = #binding{tv=TV, id=ID, exported=Exported, loc=Loc},
          define(Name, B, ModuleC);

        {N, _, TE, OptionsOrFields} when N == enum; N == struct ->
          {Loc, Name, NumParams} = case TE of
            {con_token, Loc_, Name_} -> {Loc_, Name_, 0};
            {gen_te, _, {con_token, Loc_, Name_}, ParamTEs} ->
              {Loc_, Name_, length(ParamTEs)}
          end,

          Con = utils:qualify(Name, ModuleC),
          TB = #type_binding{is_iface=false, num_params=NumParams, loc=Loc},
          ModuleC1 = define_type(Con, TB, ModuleC),

          case N of
            enum ->
              Enums = ModuleC1#ctx.enums,
              {OptionNames, ModuleC2} = lists:mapfoldl(fun(Option, NestedC) ->
                {option, _, {con_token, OptionLoc, OptionCon}, ArgTEs, _} = Option,
                {TV, ID} = tv_server:fresh_gnr_id(NestedC#ctx.pid),

                B = #binding{
                  tv=TV,
                  id=ID,
                  exported=true,
                  arity=length(ArgTEs),
                  loc=OptionLoc
                },
                NestedC1 = define(OptionCon, B, NestedC),
                {OptionCon, NestedC1}
              end, ModuleC1, OptionsOrFields),

              ModuleC2#ctx{enums=Enums#{Con => {OptionNames, none, none}}};

            struct ->
              {TV, ID} = tv_server:fresh_gnr_id(ModuleC1#ctx.pid),
              B = #binding{tv=TV, id=ID, exported=true, loc=Loc},
              ModuleC2 = define(Name, B, ModuleC1),

              {RawT, ModuleC3} = infer_sig(false, true, #{}, TE, ModuleC2),
              StructInfo = {RawT, ModuleC3#ctx.sig_vs},
              ModuleC3#ctx{structs=(ModuleC3#ctx.structs)#{Con => StructInfo}}
          end;

        {exception, _, {con_token, Loc, Name}, ArgTEs} ->
          {TV, ID} = tv_server:fresh_gnr_id(ModuleC#ctx.pid),
          B = #binding{
            tv=TV,
            id=ID,
            exported=true,
            arity=length(ArgTEs),
            loc=Loc
          },
          define(Name, B, ModuleC);

        {interface, _, {con_token, Loc, Name}, _, Fields} ->
          Con = utils:qualify(Name, ModuleC),
          NumParams = case gen_t_num_params({record_te, Loc, Fields}) of
            false -> 0;
            NumParams_ -> NumParams_
          end,
          TB = #type_binding{is_iface=true, num_params=NumParams, loc=Loc},
          ModuleC1 = define_type(Con, TB, ModuleC),

          Value = {Fields, none, ordsets:new()},
          NewIfaces = (ModuleC1#ctx.ifaces)#{Con => Value},
          NewImpls = (ModuleC1#ctx.impls)#{Con => #{}},
          ModuleC2 = ModuleC1#ctx{ifaces=NewIfaces, impls=NewImpls},

          lists:foldl(fun({sig, _, {var, VarLoc, VarName}, _}, NestedC) ->
            {TV, ID} = tv_server:fresh_gnr_id(ModuleC#ctx.pid),
            B = #binding{tv=TV, id=ID, exported=true, loc=VarLoc},
            define(VarName, B, NestedC)
          end, ModuleC2, Fields);

        _ -> ModuleC
      end
    end, FoldC#ctx{module=Module}, Defs)
  end, C, Comps).

define(Name, #binding{loc=Loc}=B, C) ->
  #ctx{module=Module, g_env=GEnv, exports=Exports} = C,
  case maps:find({Module, Name}, GEnv) of
    {ok, #binding{loc=OrigLoc}} ->
      {Err, ErrLoc} = if
        % e.g. global has the same name as a builtin
        Loc == ?BUILTIN_LOC -> {?ERR_REDEF_BUILTIN(Name), OrigLoc};
        % e.g. direct import has the same name as a builtin
        OrigLoc == ?BUILTIN_LOC -> {?ERR_REDEF_BUILTIN(Name), Loc};
        true -> {?ERR_REDEF(Name, OrigLoc), Loc}
      end,
      add_ctx_err(Err, ErrLoc, C);

    error ->
      NewExports = if
        B#binding.exported ->
          Names = maps:get(Module, Exports),
          Exports#{Module => ordsets:add_element(Name, Names)};
        true -> Exports
      end,
      C#ctx{g_env=GEnv#{{Module, Name} => B}, exports=NewExports}
  end.

define_type(Con, #type_binding{is_iface=IsIface, loc=Loc}=TB, C) ->
  #ctx{module=Module, types=Types, exports=Exports} = C,

  case maps:find(Con, Types) of
    % e.g. struct that has the same name as a builtin
    {ok, #type_binding{is_iface=true, loc=?BUILTIN_LOC}} ->
      add_ctx_err(?ERR_REDEF_BUILTIN_IFACE(Con), Loc, C);
    {ok, #type_binding{is_iface=false, loc=?BUILTIN_LOC}} ->
      add_ctx_err(?ERR_REDEF_BUILTIN_TYPE(Con), Loc, C);

    % e.g. imported type that has the same name as a builtin
    {ok, #type_binding{loc=OrigLoc}} when Loc == ?BUILTIN_LOC, IsIface ->
      add_ctx_err(?ERR_REDEF_BUILTIN_IFACE(Con), OrigLoc, C);
    {ok, #type_binding{loc=OrigLoc}} when Loc == ?BUILTIN_LOC, not IsIface ->
      add_ctx_err(?ERR_REDEF_BUILTIN_TYPE(Con), OrigLoc, C);

    {ok, #type_binding{is_iface=true, loc=OrigLoc}} ->
      add_ctx_err(?ERR_REDEF(Con, OrigLoc), Loc, C);
    {ok, #type_binding{is_iface=false, loc=OrigLoc}} ->
      add_ctx_err(?ERR_REDEF(Con, OrigLoc), Loc, C);

    error ->
      NewExports = if
        TB#type_binding.exported ->
          Names = maps:get(Module, Exports),
          RawCon = utils:unqualify(Con),
          Exports#{Module => ordsets:add_element(RawCon, Names)};
        true -> Exports
      end,
      C#ctx{types=Types#{Con => TB}, exports=NewExports}
  end.

gen_t_num_params({lam_te, _, ArgTEs, ReturnTE}) ->
  NumParams = lists:foldl(fun(ArgTE, FoldNumParams) ->
    case FoldNumParams of
      false -> gen_t_num_params(ArgTE);
      _ -> FoldNumParams
    end
  end, false, ArgTEs),
  case NumParams of
    false -> gen_t_num_params(ReturnTE);
    _ -> NumParams
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
  {GEnvs, C1} = lists:mapfoldl(fun(#comp{module=Module, deps=Deps}, FoldC) ->
    NewImportedPairs = lists:map(fun({DepModule, _}) ->
      {Module, DepModule}
    end, Deps),
    NewImported = ordsets:union(
      FoldC#ctx.imported,
      ordsets:from_list(NewImportedPairs)
    ),

    FoldC1 = FoldC#ctx{module=Module, imported=NewImported},
    FoldC2 = populate_direct_imports(Deps, FoldC1),

    % Remove direct imports from env. We don't want modules trying to import
    % recursively through other modules, as this would make the order in
    % which files are processed important.
    {FoldC2#ctx.g_env, FoldC2#ctx{g_env=FoldC#ctx.g_env}}
  end, C, Comps),

  CompsGEnvs = lists:zip(Comps, GEnvs),
  C2 = infer_ifaces(CompsGEnvs, C1),

  lists:foldl(fun({Comp, GEnv}, FoldC) ->
    #comp{module=Module, ast={module, _, _, _, Defs}} = Comp,

    {LastSig, FoldC1} = lists:foldl(fun(Node, {UncheckedSig, ModuleC}) ->
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
          #binding{tv=TV, id=ID} = g_env_get(Name, ModuleC1),
          ModuleC2 = case Expr of
            {fn, _, _, _, _} -> ModuleC1;
            _ ->
              NewGEnv = maps:remove({Module, Name}, ModuleC1#ctx.g_env),
              ModuleC1#ctx{g_env=NewGEnv}
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
          ModuleC6 = ModuleC5#ctx{g_env=ModuleC#ctx.g_env},

          case Sig of
            none -> {none, ModuleC6};
            _ ->
              % There's no active gnr right now. Inferring a signature doesn't
              % add any constraints, so this is OK.
              {SigT, ModuleC7} = infer(Sig, ModuleC6),
              case SigT of
                % Couldn't determine a valid signature. If we try to generalize,
                % we'll get a rigid TV, which will propagate errors. Instead,
                % just stop here.
                {hole, false} -> {none, ModuleC7};

                _ ->
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
              end
          end;

        _ when element(1, Node) == sig -> {Node, ModuleC1};
        _ when element(1, Node) == interface -> {none, ModuleC1};
        _ ->
          {_, ModuleC2} = infer(Node, ModuleC1),
          {none, ModuleC2}
      end
    end, {none, FoldC#ctx{module=Module, g_env=GEnv}}, Defs),

    case LastSig of
      none -> FoldC1;
      {sig, _, {var, _, SigName}, _} ->
        add_ctx_err(?ERR_SIG_NO_DEF(SigName), ?LOC(LastSig), FoldC1)
    end
  end, C2, CompsGEnvs).

populate_direct_imports(Deps, C) ->
  lists:foldl(fun({DepModule, Idents}, ModuleC) ->
    Expanded = case Idents of
      [{all, AllLoc}] -> utils:exported_idents(DepModule, AllLoc, C);
      _ -> Idents
    end,

    lists:foldl(fun(Ident, NestedC) ->
      case Ident of
        {var, Loc, Name} ->
          {B, NestedC1} = lookup(DepModule, Name, Loc, NestedC),
          define(Name, B#binding{exported=false, loc=Loc}, NestedC1);

        {con_token, Loc, Name} ->
          Con = lists:concat([DepModule, '.', Name]),
          {TypeExists, NestedC1} = case maps:find(Con, NestedC#ctx.types) of
            {ok, #type_binding{exported=true, num_params=NumParams}=TB} ->
              NewCon = utils:qualify(Name, NestedC),
              NewTB = TB#type_binding{exported=false, loc=Loc},

              CaseC = define_type(NewCon, NewTB, NestedC),
              CaseC1 = case {no_ctx_errs(CaseC, NestedC), NumParams} of
                % use the error message from define_type
                {false, _} -> CaseC;

                {true, 0} -> add_alias(NewCon, [], {con, Con}, false, CaseC);
                {true, _} ->
                  Vs = lists:map(fun(_) ->
                    tv_server:fresh(CaseC#ctx.pid)
                  end, lists:seq(1, NumParams)),
                  add_alias(NewCon, Vs, {gen, {con, Con}, Vs}, false, CaseC)
              end,

              {true, CaseC1};

            error -> {false, NestedC}
          end,

          {B, NestedC2} = lookup(DepModule, Name, Loc, NestedC1),
          case {TypeExists, no_ctx_errs(NestedC2, NestedC1)} of
            {false, false} -> NestedC2;
            {true, false} -> NestedC1;
            {_, true} ->
              define(Name, B#binding{exported=false, loc=Loc}, NestedC2)
          end;

        {variants, Loc, Name} ->
          Con = lists:concat([DepModule, '.', Name]),
          case maps:find(Con, NestedC#ctx.enums) of
            {ok, {OptionNames, _, _}} ->
              lists:foldl(fun(OptionName, #ctx{g_env=GEnv}=FoldC) ->
                B = maps:get({DepModule, OptionName}, GEnv),
                define(OptionName, B#binding{exported=false, loc=Loc}, FoldC)
              end, NestedC, OptionNames);

            error ->
              add_ctx_err(?ERR_NOT_DEF_TYPE(Con, DepModule), Loc, NestedC)
          end
      end
    end, ModuleC, Expanded)
  end, C, Deps).

infer_ifaces(CompsGEnvs, C) ->
  % Before inference, we need to first populate the inheritance tree. This
  % ensures sig inference will correctly consolidate interfaces within the
  % same family.
  C1 = lists:foldl(fun({Comp, GEnv}, FoldC) ->
    #comp{module=Module, ast={module, _, _, _, Defs}} = Comp,

    lists:foldl(fun(Node, ModuleC) ->
      case Node of
        {interface, _, {con_token, _, RawCon}, Extends, Fields} ->
          Con = utils:qualify(RawCon, ModuleC),
          #type_binding{
            is_iface=true,
            num_params=NumParams
          } = maps:get(Con, ModuleC#ctx.types),

          {Parents, ModuleC1} = lists:foldl(fun(ConToken, Memo) ->
            {FoldParents, NestedC} = Memo,
            {con_token, ParentLoc, ParentRawCon} = ConToken,

            ParentCon = utils:resolve_con(ParentRawCon, NestedC),
            NestedC1 = validate_type(
              ParentCon,
              true,
              NumParams,
              ParentLoc,
              NestedC
            ),

            case no_ctx_errs(NestedC1, NestedC) of
              false -> {FoldParents, NestedC1};
              true ->
                ParentFamily = utils:family_is(ParentCon, NestedC1#ctx.ifaces),
                case ordsets:is_element(Con, ParentFamily) of
                  false -> {ordsets:add_element(ParentCon, FoldParents), NestedC1};
                  true ->
                    NestedC2 = add_ctx_err(
                      ?ERR_CYCLE(Con, ParentCon),
                      ParentLoc,
                      NestedC1
                    ),
                    {FoldParents, NestedC2}
                end
            end
          end, {ordsets:new(), ModuleC}, Extends),

          Ifaces = ModuleC1#ctx.ifaces,
          NewIfaces = Ifaces#{Con => {Fields, none, Parents}},
          ModuleC1#ctx{ifaces=NewIfaces};

        _ -> ModuleC
      end
    end, FoldC#ctx{module=Module, g_env=GEnv}, Defs)
  end, C, CompsGEnvs),

  lists:foldl(fun({Comp, GEnv}, FoldC) ->
    #comp{module=Module, ast={module, _, _, _, Defs}} = Comp,

    lists:foldl(fun(Node, ModuleC) ->
      if
        element(1, Node) == interface ->
          {_, ModuleC1} = infer(Node, ModuleC),
          ModuleC1;
        true -> ModuleC
      end
    end, FoldC#ctx{module=Module, g_env=GEnv}, Defs)
  end, C1, CompsGEnvs).

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
  Names = ordsets:union(lists:map(fun pattern_names/1, Args)),
  C1 = ordsets:fold(fun(Name, FoldC) ->
    TV = tv_server:fresh(FoldC#ctx.pid),
    l_env_add(Name, #binding{tv=TV}, FoldC)
  end, C, Names),

  {ArgTsRev, C2} = lists:foldl(fun(Pattern, {Ts, FoldC}) ->
    {PatternT, FoldC1} = infer(Pattern, FoldC),
    {[PatternT | Ts], FoldC1}
  end, {[], C1}, Args),

  % Any interfaces from the return type will be in the environment during code
  % gen. To avoid must solve errors, we treat them as bound variables by adding
  % the return type to the env. The key doesn't matter, so we just use the
  % unique ref for this function.
  ReturnTV = tv_server:fresh(C2#ctx.pid),
  C3 = l_env_add(Ref, #binding{tv=ReturnTV}, C2),
  {ReturnT, C4} = infer(Expr, C3),
  C5 = add_cst(ReturnTV, ReturnT, ?LOC(Expr), "return type", C4),

  T = {lam, lists:reverse(ArgTsRev), ReturnT},
  FnRefs = C5#ctx.fn_refs,
  % keep reference of original local env to find bound variables
  C6 = C5#ctx{fn_refs=FnRefs#{Ref => {T, C#ctx.l_env}}},

  % restore original env
  {T, C6#ctx{l_env=C#ctx.l_env}};

infer({sig, _, _, Sig}, C) ->
  {SigT, C1} = infer_sig(false, false, #{}, Sig, C),
  {NormT, _} = norm_sig_type(SigT, false, C1#ctx.pid),
  {NormT, C1};

infer({expr_sig, Loc, Ref, Expr, Sig}, C) ->
  G = C#ctx.gnr,
  {TV, ID} = tv_server:fresh_gnr_id(C#ctx.pid),

  {ExprT, C1} = infer(Expr, new_gnr(TV, ID, C)),
  {SigT, C2} = infer_sig(false, false, #{}, Sig, C1),
  {NormT, _} = norm_sig_type(SigT, false, C2#ctx.pid),

  C3 = add_cst(TV, ExprT, ?LOC(Expr), ?FROM_EXPR_SIG, C2),
  C4 = add_cst(TV, NormT, Loc, ?FROM_EXPR_SIG, C3),
  C5 = finish_gnr(C4, add_gnr_dep(ID, G)),

  % We don't want to return {inst, ...} directly; if it's added to two separate
  % constraints, that will cause two separate instantiations. Additionally, we
  % want all returned types to be fully resolved in case they're associated with
  % a reference. To accomplish this, introduce an intermediate TV that will get
  % assigned the inst.
  InstTV = tv_server:fresh(C5#ctx.pid),
  C6 = add_cst(InstTV, {inst, Ref, TV}, Loc, ?FROM_EXPR_SIG_RESULT, C5),

  {InstTV, C6};

infer({enum, _, EnumTE, Options}, C) ->
  {RawT, C1} = infer_sig(false, true, #{}, EnumTE, C),
  SigVs = C1#ctx.sig_vs,
  FVs = fvs(RawT),

  {GenOptions, _, C2} = lists:foldl(fun(Option, {FoldGenOptions, Keys, FoldC}) ->
    {option, _, {con_token, Loc, Con}, _, KeyNode} = Option,
    {OptionT, ArgTs, FoldC1} = infer_option(Option, RawT, FVs, SigVs, FoldC),

    Key = case KeyNode of
      'None' -> list_to_atom(Con);
      {'Some', {atom, _, Key_}} -> Key_
    end,

    NewGenOptions = case ordsets:size(fvs(OptionT)) == 0 of
      true -> FoldGenOptions;
      false ->
        TupleT = {tuple, [{con, "Atom"} | ArgTs]},
        [{Key, TupleT} | FoldGenOptions]
    end,

    {NewKeys, FoldC2} = case KeyNode of
      'None' ->
        case maps:find(Key, Keys) of
          % We've already added an ERR_REDEF for the option. There's no need to
          % add an ERR_DUP_KEY as well.
          {ok, {default, _, _}} -> {Keys, FoldC1};

          {ok, {custom, _, CustomLoc}} ->
            CaseC = add_ctx_err(
              ?ERR_DUP_KEY(Key, Con, Loc),
              CustomLoc,
              FoldC1
            ),
            {Keys, CaseC};
          error -> {Keys#{Key => {default, Con, Loc}}, FoldC1}
        end;

      {'Some', {atom, KeyLoc, _}} ->
        case maps:find(Key, Keys) of
          {ok, {_, OtherCon, OtherLoc}} ->
            CaseC = add_ctx_err(
              ?ERR_DUP_KEY(Key, OtherCon, OtherLoc),
              KeyLoc,
              FoldC1
            ),

            % In case the map contains a default, we go ahead and replace the
            % value with a custom. This way, if another default comes up, we'll
            % correctly report an error.
            {Keys#{Key := {custom, Con, KeyLoc}}, CaseC};
          error -> {Keys#{Key => {custom, Con, KeyLoc}}, FoldC1}
        end
    end,

    {NewGenOptions, NewKeys, FoldC2}
  end, {[], #{}, C1}, Options),

  {Con, Vs} = case RawT of
    {con, Con_} -> {Con_, []};
    {gen, {con, Con_}, ParamTs} ->
      {Con_, lists:map(fun({tv, V, none, _}) -> V end, ParamTs)}
  end,

  Enums = C2#ctx.enums,
  {OptionNames, none, none} = maps:get(Con, Enums),
  NewEnums = Enums#{Con => {OptionNames, Vs, GenOptions}},
  {none, C2#ctx{enums=NewEnums}};

infer({exception, Loc, ConToken, ArgTEs}, C) ->
  Option = {option, Loc, ConToken, ArgTEs, none},
  {_, _, C1} = infer_option(Option, {con, "Exception"}, ordsets:new(), #{}, C),
  {none, C1};

infer({struct, Loc, StructTE, Fields}, C) ->
  Name = case StructTE of
    {con_token, _, Name_} -> Name_;
    {gen_te, _, {con_token, _, Name_}, _} -> Name_
  end,
  Con = utils:qualify(Name, C),

  {RawT, SigVs} = maps:get(Con, C#ctx.structs),
  {{record, _, RawFieldMap}, C1} = infer_sig(
    {RawT, fvs(RawT)},
    false,
    SigVs,
    {record_te, Loc, Fields},
    C
  ),

  RawFieldTs = lists:map(fun({sig, _, {var, _, FieldName}, _}) ->
    maps:get(FieldName, RawFieldMap)
  end, Fields),
  {FnT, _} = norm_sig_type({lam, RawFieldTs, RawT}, false, C1#ctx.pid),

  Vs = case RawT of
    {con, _} -> [];
    {gen, _, ParamTs} -> lists:map(fun({tv, V, none, _}) -> V end, ParamTs)
  end,
  C2 = add_alias(Con, Vs, {record, none, RawFieldMap}, true, C1),

  #binding{tv=TV, id=ID} = g_env_get(Name, C2),
  C3 = new_gnr(TV, ID, C2),
  C4 = add_cst(TV, FnT, Loc, ?FROM_STRUCT_CTOR, C3),
  C5 = finish_gnr(C4, C2#ctx.gnr),

  {none, C5};

infer({interface, _, {con_token, _, RawCon}, _, Fields}, C) ->
  Con = utils:qualify(RawCon, C),
  #type_binding{
    is_iface=true,
    num_params=NumParams
  } = maps:get(Con, C#ctx.types),

  Ifaces = C#ctx.ifaces,
  Ancestors = ordsets:subtract(
    ordsets:del_element(Con, utils:family_is(Con, Ifaces)),
    utils:builtin_is()
  ),
  FieldOrigins = ordsets:fold(fun(AncestorCon, FoldFieldOrigins) ->
    {AncestorFields, _, _} = maps:get(AncestorCon, Ifaces),
    lists:foldl(fun({sig, _, {var, _, Name}, _}, NestedFieldOrigins) ->
      NestedFieldOrigins#{Name => AncestorCon}
    end, FoldFieldOrigins, AncestorFields)
  end, #{}, Ancestors),

  % type sigs don't need consolidation, so don't pass aliases
  SubOpts = #sub_opts{subs=#{"T" => {set_ifaces, ordsets:from_list([Con])}}},
  SigVs = #{"T" => {none, NumParams}},

  {FieldTs, C1} = lists:mapfoldl(fun(Sig, FoldC) ->
    {sig, FieldLoc, {var, _, Name}, FieldTE} = Sig,
    FoldC1 = case maps:find(Name, FieldOrigins) of
      error -> FoldC;
      {ok, ParentCon} ->
        Err = ?ERR_DUP_FIELD_PARENT(Name, ParentCon),
        add_ctx_err(Err, FieldLoc, FoldC)
    end,
    FoldC2 = case {FieldTE, gen_t_num_params(FieldTE)} of
      {{lam_te, _, _, _}, N} when N /= false -> FoldC1;
      _ -> add_ctx_err(?ERR_IFACE_TYPE(Name), FieldLoc, FoldC1)
    end,

    {SigT, FoldC3} = infer_sig(false, false, SigVs, FieldTE, FoldC2),
    RawT = utils:subs(SigT, SubOpts),
    {T, _} = norm_sig_type(RawT, false, FoldC3#ctx.pid),

    #binding{tv=TV, id=ID} = g_env_get(Name, FoldC3),
    FoldC4 = new_gnr(TV, ID, FoldC3),
    FoldC5 = add_cst(TV, T, FieldLoc, ?FROM_GLOBAL_SIG(Name), FoldC4),
    {RawT, finish_gnr(FoldC5, FoldC3#ctx.gnr)}
  end, C, Fields),

  Value = setelement(2, maps:get(Con, Ifaces), FieldTs),
  NewIfaces = Ifaces#{Con => Value},
  {none, C1#ctx{ifaces=NewIfaces}};

infer({impl, Loc, Ref, {con_token, IfaceLoc, RawIfaceCon}, ImplTE, Inits}, C) ->
  ImplLoc = ?LOC(ImplTE),
  IfaceCon = utils:resolve_con(RawIfaceCon, C),

  case maps:find(IfaceCon, C#ctx.ifaces) of
    % TODO: are builtin type classes implementable?
    error -> {none, add_ctx_err(?ERR_NOT_DEF_IFACE(IfaceCon), IfaceLoc, C)};

    {ok, {Fields, FieldTs, Parents}} ->
      #type_binding{
        is_iface=true,
        num_params=IfaceNumParams
      } = maps:get(IfaceCon, C#ctx.types),

      {RawT, C1} = case {IfaceNumParams, ImplTE} of
        {0, _} -> infer_sig(false, false, #{}, ImplTE, C);

        {_, {con_token, ConLoc, RawCon}} ->
          Con = utils:resolve_con(RawCon, C),
          NumParams = case maps:find(Con, C#ctx.types) of
            {ok, #type_binding{num_params=Num}}
              when IfaceNumParams == 1 andalso Num > 1 -> Num;
            {ok, #type_binding{num_params=1}} when IfaceNumParams > 1 -> 1;
            _ -> IfaceNumParams
          end,

          ValidatedC = validate_type(Con, false, NumParams, ConLoc, C),
          case no_ctx_errs(ValidatedC, C) of
            false -> {none, ValidatedC};
            true ->
              ParamTs = lists:map(fun(_) -> unit end, lists:seq(1, NumParams)),
              GenT = {gen, {con, Con}, ParamTs},
              {gen, ConT, _} = unalias_except_struct(
                GenT,
                ValidatedC#ctx.aliases
              ),
              {ConT, ValidatedC}
          end;

        _ -> {none, add_ctx_err(?ERR_IMPL_TYPE(IfaceCon), ImplLoc, C)}
      end,

      case no_ctx_errs(C1, C) of
        false -> {none, C1};
        true ->
          {ImplT, _} = norm_sig_type(RawT, false, C1#ctx.pid),
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
              NewImpls = Impls#{IfaceCon => NewSubImpls},
              CaseC = C1#ctx{impls=NewImpls},

              V = tv_server:next_name(CaseC#ctx.pid),
              GVs = ordsets:from_list([V]),

              EmptySet = ordsets:new(),
              InstTV = case Parents of
                EmptySet -> {inst, Ref, GVs, {tv, V, none, false}};
                _ -> {inst, Ref, GVs, {tv, V, Parents, false}}
              end,

              From = ?FROM_PARENT_IFACES,
              CaseC1 = add_cst(ImplT, InstTV, ImplLoc, From, new_gnr(CaseC)),
              finish_gnr(CaseC1, CaseC#ctx.gnr)
          end,

          Pairs = lists:map(fun({Sig, FieldT}) ->
            {sig, FieldLoc, {var, _, Name}, _} = Sig,
            {Name, {FieldLoc, FieldT}}
          end, lists:zip(Fields, FieldTs)),
          FieldLocTs = maps:from_list(Pairs),

          {ActualNames, C3} = infer_impl_inits(
            Inits,
            ImplT,
            ImplLoc,
            IfaceCon,
            IfaceNumParams,
            FieldLocTs,
            C2
          ),

          ExpNames = ordsets:from_list(maps:keys(FieldLocTs)),
          MissingNames = ordsets:subtract(ExpNames, ActualNames),

          C4 = ordsets:fold(fun(Name, FoldC) ->
            add_ctx_err(?ERR_MISSING_FIELD_IMPL(Name, IfaceCon), Loc, FoldC)
          end, C3, MissingNames),
          ImplRefs = C4#ctx.impl_refs,
          {none, C4#ctx{impl_refs=ImplRefs#{Ref => Key}}}
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

infer({map, _, Assocs}, C) ->
  KeyTV = tv_server:fresh(C#ctx.pid),
  ValueTV = tv_server:fresh(C#ctx.pid),

  C1 = lists:foldl(fun({assoc, _, Key, Value}, FoldC) ->
    {KeyT, FoldC1} = infer(Key, FoldC),
    FoldC2 = add_cst(KeyT, KeyTV, ?LOC(Key), ?FROM_MAP_KEY, FoldC1),
    {ValueT, FoldC3} = infer(Value, FoldC2),
    add_cst(ValueT, ValueTV, ?LOC(Value), ?FROM_MAP_VALUE, FoldC3)
  end, C, Assocs),

  {{gen, {con, "Map"}, [KeyTV, ValueTV]}, C1};

infer({N, Loc, Name}, C) when N == var; N == con_token; N == var_value ->
  lookup_inst(Name, Loc, none, C);

infer({var_ref, Loc, Ref, Name}, C) -> lookup_inst(Name, Loc, Ref, C);


% Holes are underscores in exprs that the user can introduce to "ask" the type
% system what type it needs.
infer({hole, _}, C) -> {{hole, true}, C};

% Underscores in patterns are used to match anything.
infer({'_', _}, C) -> {tv_server:fresh(C#ctx.pid), C};

infer({anon_record, _, Ref, Inits}, #ctx{record_refs=RecordRefs}=C) ->
  {FieldMap, C1} = lists:foldl(fun(Init, {Map, FoldC}) ->
    {init, _, {var, Loc, Name}, Expr} = Init,

    {T, FoldC1} = case Expr of
      {fn, FnLoc, _, _, _} ->
        TV = tv_server:fresh(FoldC#ctx.pid),
        CaseC = l_env_add(Name, #binding{tv=TV}, FoldC),
        {ExprT, CaseC1} = infer(Expr, CaseC),

        CaseC2 = add_cst(TV, ExprT, FnLoc, ?FROM_FIELD_DEF(Name), CaseC1),
        {TV, CaseC2#ctx{l_env=FoldC#ctx.l_env}};

      _ -> infer(Expr, FoldC)
    end,

    case maps:is_key(Name, Map) of
      true -> {Map, add_ctx_err(?ERR_DUP_FIELD(Name), Loc, FoldC1)};
      false -> {Map#{Name => T}, FoldC1}
    end
  end, {#{}, C}, Inits),

  RecordT = {record, tv_server:next_name(C1#ctx.pid), FieldMap},
  C2 = case Ref of
    none -> C1;
    _ -> C1#ctx{record_refs=RecordRefs#{Ref => RecordT}}
  end,
  {RecordT, C2};

infer({anon_record_ext, Loc, Ref, Expr, AllInits}, C) ->
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
      {{record, A, FieldMap}, C2} = infer({anon_record, Loc, none, Inits}, C1),
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
      {{record, ExtA, Ext}, C4} = infer({anon_record, Loc, none, ExtInits}, C3),
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

      RecordT = {record_ext, tv_server:next_name(C5#ctx.pid), ExprT, Ext},
      RecordRefs = C5#ctx.record_refs,
      C6 = case Ref of
        none -> C5;
        _ -> C5#ctx{record_refs=RecordRefs#{Ref => RecordT}}
      end,
      {RecordT, C6}
  end;

infer({record, Loc, {con_token, ConLoc, RawCon}, Inits}, C) ->
  Con = utils:resolve_con(RawCon, C),
  case maps:find(Con, C#ctx.types) of
    {ok, #type_binding{is_iface=false, num_params=NumParams}} ->
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

      {RecordT, C1} = infer({anon_record, Loc, none, Inits}, C),
      From = ?FROM_RECORD_CREATE(Con),

      TV = tv_server:fresh(C1#ctx.pid),
      C2 = add_cst(TV, RecordT, Loc, From, C1),
      C3 = add_cst(TV, ExpT, Loc, From, C2),
      {TV, C3};

    {ok, #type_binding{is_iface=true}} ->
      {RecordT, C1} = infer({anon_record, Loc, none, Inits}, C),
      {RecordT, add_ctx_err(?ERR_IFACE_NOT_TYPE(Con), ConLoc, C1)};

    error ->
      {RecordT, C1} = infer({anon_record, Loc, none, Inits}, C),
      {RecordT, add_ctx_err(?ERR_NOT_DEF_TYPE(Con), ConLoc, C1)}
  end;

infer({record_ext, Loc, {con_token, ConLoc, RawCon}, Expr, AllInits}, C) ->
  Con = utils:resolve_con(RawCon, C),
  case maps:find(Con, C#ctx.types) of
    {ok, #type_binding{is_iface=false, num_params=NumParams}} ->
      ExpT = case NumParams of
        0 -> unalias_except_struct({con, Con}, C#ctx.aliases);
        _ ->
          Vs = lists:map(fun(_) ->
            tv_server:fresh(C#ctx.pid)
          end, lists:seq(1, NumParams)),
          unalias_except_struct({gen, {con, Con}, Vs}, C#ctx.aliases)
      end,

      {RecordT, C1} = infer({anon_record_ext, Loc, none, Expr, AllInits}, C),
      From = ?FROM_RECORD_UPDATE,

      TV = tv_server:fresh(C1#ctx.pid),
      C2 = add_cst(TV, RecordT, Loc, From, C1),
      C3 = add_cst(TV, ExpT, Loc, From, C2),
      {TV, C3};

    {ok, #type_binding{is_iface=true}} ->
      {RecordT, C1} = infer({anon_record_ext, Loc, none, Expr, AllInits}, C),
      {RecordT, add_ctx_err(?ERR_IFACE_NOT_TYPE(Con), ConLoc, C1)};

    error ->
      {RecordT, C1} = infer({anon_record_ext, Loc, none, Expr, AllInits}, C),
      {RecordT, add_ctx_err(?ERR_NOT_DEF_TYPE(Con), ConLoc, C1)}
  end;

infer({field_fn, _, {var, _, Name}}, C) ->
  FieldTV = tv_server:fresh(C#ctx.pid),
  BaseTV = tv_server:fresh(C#ctx.pid),
  A = tv_server:next_name(C#ctx.pid),
  RecordExtT = {record_ext, A, BaseTV, #{Name => FieldTV}},
  {{lam, [RecordExtT], FieldTV}, C};

infer({field, Loc, Expr, Prop}, C) ->
  case Expr of
    {con_token, ConLoc, Module} ->
      {Ref, Name} = case Prop of
        {var_ref, _, Ref_, Name_} -> {Ref_, Name_};
        {con_token, _, Name_} -> {none, Name_}
      end,

      case ordsets:is_element({C#ctx.module, Module}, C#ctx.imported) of
        true -> lookup_inst(Module, Name, Loc, Ref, C);
        false ->
          TV = tv_server:fresh(C#ctx.pid),
          {TV, add_ctx_err(?ERR_NOT_DEF_MODULE(Module), ConLoc, C)}
      end;

    _ ->
      {ExprT, C1} = infer(Expr, C),
      {var, PropLoc, Name} = Prop,
      FieldFn = {field_fn, PropLoc, Prop},
      {{lam, [RecordExtT], ResultT}, C2} = infer(FieldFn, C1),

      From = ?FROM_FIELD_ACCESS(Name),
      C3 = add_cst(ExprT, RecordExtT, Loc, From, C2),
      {ResultT, C3}
  end;

infer({app, Loc, Expr, Args}, C) ->
  {ExprT, C1} = infer(Expr, C),
  {ProvidedRev, HoleTsRev, C2} = lists:foldl(fun(Arg, Memo) ->
    {FoldProvided, FoldHoleTs, FoldC} = Memo,
    {T, FoldC1} = case Arg of
      {hole, _} -> {tv_server:fresh(FoldC#ctx.pid), FoldC};
      _ -> infer(Arg, FoldC)
    end,

    ArgLoc = ?LOC(Arg),
    {NewProvided, NewHoleTs} = case Arg of
      {hole, _} -> {[{hole, ArgLoc, T} | FoldProvided], [T | FoldHoleTs]};
      _ -> {[{arg, ArgLoc, T} | FoldProvided], FoldHoleTs}
    end,
    {NewProvided, NewHoleTs, FoldC1}
  end, {[], [], C1}, Args),

  TV = tv_server:fresh(C2#ctx.pid),
  T = {lam, C2#ctx.l_env, lists:reverse(ProvidedRev), TV},

  ResultT = case HoleTsRev of
    [] -> TV;
    _ -> {lam, lists:reverse(HoleTsRev), TV}
  end,
  C3 = add_cst(T, ExprT, Loc, ?FROM_APP, C2),
  {ResultT, C3};

infer({variant, Loc, Expr, Args}, C) ->
  {ConLoc, Con, {B, C1}} = case Expr of
    {field, ConLoc_, {con_token, _, Module}, {con_token, _, Con_}} ->
      {ConLoc_, Con_, lookup(Module, Con_, ConLoc_, C)};
    {con_token, ConLoc_, Con_} -> {ConLoc_, Con_, lookup(Con_, ConLoc_, C)}
  end,

  case no_ctx_errs(C1, C) of
    false -> {tv_server:fresh(C1#ctx.pid), C1};
    true ->
      case {B#binding.arity, length(Args)} of
        {undefined, _} ->
          TV = tv_server:fresh(C1#ctx.pid),
          {TV, add_ctx_err(?ERR_MATCH_STRUCT, ConLoc, C1)};
        {Arity, Arity} when Arity == 0 -> infer(Expr, C1);
        {Arity, Arity} -> infer({app, Loc, Expr, Args}, C1);
        {ExpArity, Arity} ->
          TV = tv_server:fresh(C1#ctx.pid),
          {TV, add_ctx_err(?ERR_OPTION_ARITY(Con, ExpArity, Arity), Loc, C1)}
      end
  end;

infer({native, Loc, {atom, _, Module}, {var, _, Name}, Arity}, C) ->
  % For now, ignore return value. We'll get a native function error below if
  % this fails.
  code:ensure_loaded(Module),

  C1 = case erlang:function_exported(Module, list_to_atom(Name), Arity) of
    true -> C;
    false -> add_ctx_err(?ERR_NOT_DEF_NATIVE(Module, Name, Arity), Loc, C)
  end,

  ArgTs = [tv_server:fresh(C1#ctx.pid) || _ <- lists:seq(1, Arity)],
  {{lam, ArgTs, tv_server:fresh(C1#ctx.pid)}, C1};

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
  {T, C2#ctx{l_env=C#ctx.l_env}};

infer({if_let, _, Pattern, Expr, Then, Else}, C) ->
  C1 = infer_pattern(Pattern, Expr, ?FROM_IF_LET_PATTERN, C),
  {ThenT, C2} = infer(Then, C1),
  % revert env to before pattern was parsed
  C3 = C2#ctx{l_env=C#ctx.l_env},

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
  {ExprTV, ID} = tv_server:fresh_gnr_id(C#ctx.pid),
  {ExprT, C1} = infer(Expr, new_gnr(ExprTV, ID, C)),
  C2 = add_cst(ExprTV, ExprT, ?LOC(Expr), ?FROM_MATCH_HEAD, C1),
  C3 = finish_gnr(C2, add_gnr_dep(ID, C#ctx.gnr)),

  ResultTV = tv_server:fresh(C3#ctx.pid),
  C4 = lists:foldl(fun({'case', _, Pattern, Then}, FoldC) ->
    % Need a new gnr for pattern bindings (see with_pattern_env).
    FoldC1 = FoldC#ctx{gnr=add_gnr_dep(ID, (new_gnr(FoldC))#ctx.gnr)},
    PatternID = FoldC1#ctx.gnr#gnr.id,
    {PatternT, FoldC2} = infer(Pattern, with_pattern_env(Pattern, FoldC1)),

    FoldC3 = add_cst(
      % The ref here doesn't matter, as it never needs to be used for rewriting.
      % It's possible for a pattern to solve an IV with a var_value, but:
      %
      % a) Either that IV came from an inst of an already generalized fn, at
      % which point it won't be used again.
      %
      % b) Or that IV didn't come from a generalized variable, at which point
      % it'll be solved for a concrete type that doesn't need an impl.
      {inst, make_ref(), ExprTV},
      PatternT,
      ?LOC(Pattern),
      ?FROM_MATCH_PATTERN,
      FoldC2
    ),
    FoldC4 = finish_gnr(FoldC3, add_gnr_dep(PatternID, FoldC#ctx.gnr)),

    {ThenT, FoldC5} = infer(Then, FoldC4),
    % revert env to before pattern was parsed
    FoldC6 = FoldC5#ctx{l_env=FoldC#ctx.l_env},
    add_cst(ResultTV, ThenT, ?LOC(Then), ?FROM_MATCH_BODY, FoldC6)
  end, C3, Cases),

  {ResultTV, C4};

infer({'try', _, Expr, Cases}, C) ->
  {ExprT, C1} = infer(Expr, C),

  C2 = lists:foldl(fun({'case', _, Pattern, Then}, FoldC) ->
    FoldC1 = new_gnr(FoldC),
    ID = FoldC1#ctx.gnr#gnr.id,
    {PatternT, FoldC2} = infer(Pattern, with_pattern_env(Pattern, FoldC1)),
    FoldC3 = add_cst(
      {con, "Exception"},
      PatternT,
      ?LOC(Pattern),
      ?FROM_MATCH_PATTERN,
      FoldC2
    ),

    FoldC4 = finish_gnr(FoldC3, add_gnr_dep(ID, FoldC#ctx.gnr)),
    {ThenT, FoldC5} = infer(Then, FoldC4),
    % revert env to before pattern was parsed
    FoldC6 = FoldC5#ctx{l_env=FoldC#ctx.l_env},
    add_cst(ExprT, ThenT, ?LOC(Then), ?FROM_MATCH_BODY, FoldC6)
  end, C1, Cases),

  {ExprT, C2};

infer({ensure, _, Expr, After}, C) ->
  {_, C1} = infer(Expr, C),
  infer(After, C1);

infer({block, _, Exprs}, C) ->
  {T, C1} = lists:foldl(fun(Expr, {_, FoldC}) ->
    infer(Expr, FoldC)
  end, {unit, C}, Exprs),
  {T, C1};

infer({binary_op, _, '|>', Left, Right}, C) ->
  App = case Right of
    {app, Loc, Expr, Args} -> {app, Loc, Expr, Args ++ [Left]};
    _ -> {app, ?LOC(Right), Right, [Left]}
  end,
  infer(App, C);

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
      OrdTV = tv_server:fresh("Ord", C2#ctx.pid),
      {OrdTV, OrdTV, {con, "Bool"}};
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
    Op == 'raise' -> {{con, "Exception"}, tv_server:fresh(C1#ctx.pid)};
    Op == 'discard' -> {ExprT, unit};
    Op == 'assume' -> {ExprT, tv_server:fresh(C1#ctx.pid)};

    Op == 'test' -> {{con, "Assertion"}, {con, "Test"}};
    Op == 'assert' ->
      case Expr of
        % assert let with one binding and no body turns into an assertion
        {'let', LetLoc, Bindings, {unit, LetLoc}} when length(Bindings) == 1 ->
          {ExprT, {con, "Assertion"}};
        % otherwise, assert let leaves the body type unchanged
        {'let', _, _, _} -> {ExprT, ExprT};
        % assert without let turns a boolean expression into an assertion
        _ -> {{con, "Bool"}, {con, "Assertion"}}
      end
  end,

  C2 = add_cst(ExpExprT, ExprT, ?LOC(Expr), ?FROM_UNARY_OP(Op), C1),
  C3 = add_cst(ResultT, TV, Loc, ?FROM_OP_RESULT(Op), C2),
  {TV, C3}.

infer_sig(RestrictVs, Unique, SigVs, Sig, C) ->
  C1 = C#ctx{sig_vs=SigVs},
  infer_sig_helper(RestrictVs, Unique, Sig, C1).

infer_sig_helper(RestrictVs, Unique, {lam_te, _, ArgTEs, ReturnTE}, C) ->
  {ArgTs, C1} = lists:mapfoldl(fun(ArgTE, FoldC) ->
    infer_sig_helper(RestrictVs, Unique, ArgTE, FoldC)
  end, C, ArgTEs),
  {ReturnT, C2} = infer_sig_helper(RestrictVs, Unique, ReturnTE, C1),
  {{lam, ArgTs, ReturnT}, C2};
infer_sig_helper(RestrictVs, Unique, {tuple_te, _, ElemTEs}, C) ->
  {ElemTs, C1} = lists:mapfoldl(fun(TE, FoldC) ->
    infer_sig_helper(RestrictVs, Unique, TE, FoldC)
  end, C, ElemTEs),
  {{tuple, ElemTs}, C1};
infer_sig_helper(RestrictVs, Unique, {gen_te, Loc, BaseTE, ParamTEs}, C) ->
  NumParams = length(ParamTEs),

  {BaseT, AllIs, C1} = case BaseTE of
    {con_token, _, RawCon} ->
      Con = utils:resolve_con(RawCon, C),
      CaseC = case Unique of
        false -> validate_type(Con, false, NumParams, Loc, C);
        % We're inferring a new type, so don't do validation. Name conflicts for
        % new types are handled earlier.
        true -> C
      end,
      {{con, Con}, none, CaseC};

    {tv_te, TVLoc, V, IfaceTokens} ->
      {BaseIfaceTokens, GenIs} = case IfaceTokens of
        [] -> {[], none};
        _ ->
          {BaseIfaceTokens_, GenIsSet} = lists:foldr(fun(ConToken, Memo) ->
            {FoldBaseIfaceTokens, FoldGenIsSet} = Memo,
            {con_token, _, RawI} = ConToken,
            I = utils:resolve_con(RawI, C),

            case maps:find(I, C#ctx.types) of
              {ok, #type_binding{is_iface=true, num_params=0}} ->
                {FoldBaseIfaceTokens, ordsets:add_element(I, FoldGenIsSet)};
              _ -> {[ConToken | FoldBaseIfaceTokens], FoldGenIsSet}
            end
          end, {[], ordsets:new()}, IfaceTokens),

          GenIs_ = case ordsets:size(GenIsSet) == 0 of
            true -> none;
            false -> GenIsSet
          end,
          {BaseIfaceTokens_, GenIs_}
      end,

      CaseC = C#ctx{num_params=NumParams},
      {BaseT_, CaseC1} = infer_sig_helper(
        RestrictVs,
        Unique,
        {tv_te, TVLoc, V, BaseIfaceTokens},
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
          % merge AllIs with itself to consolidate Is within the same family
          Is = merge_is(AllIs, AllIs, C2#ctx.ifaces),
          {gen, NewV, Is, BaseT, ParamTs};

        _ -> unalias_except_struct({gen, BaseT, ParamTs}, C2#ctx.aliases)
      end,
      {T, C2};

    true -> {{hole, false}, C2}
  end;
infer_sig_helper(RestrictVs, Unique, {tv_te, Loc, V, IfaceTokens}, C) ->
  C1 = case RestrictVs of
    false -> C;
    {T, AllowedVs} ->
      case ordsets:is_element(V, AllowedVs) of
        true -> C;
        false ->
          case T of
            % T is already an invalid type; no need to add another error
            {tv, _, _, _} -> C;
            _ ->
              Err = case T of
                {con, "Exception"} -> ?ERR_TV_SCOPE(V);
                _ -> ?ERR_TV_SCOPE(V, element(2, T))
              end,
              add_ctx_err(Err, Loc, C)
          end
      end
  end,

  NumParams = case C1#ctx.num_params of
    undefined -> 0;
    NumParams_ -> NumParams_
  end,

  {AllIs, C2} = case IfaceTokens of
    [] -> {none, C1};
    _ ->
      lists:foldl(fun({con_token, ConLoc, RawI_}, {FoldIs, FoldC}) ->
        I = utils:resolve_con(RawI_, C1),
        NewFoldIs = ordsets:add_element(I, FoldIs),
        {NewFoldIs, validate_type(I, true, NumParams, ConLoc, FoldC)}
      end, {ordsets:new(), C1}, IfaceTokens)
  end,

  case no_ctx_errs(C1, C2) of
    true ->
      % merge AllIs with itself to consolidate Is within the same family
      Is = merge_is(AllIs, AllIs, C2#ctx.ifaces),

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

      {{tv, V, Is, true}, C3};

    false -> {{hole, false}, C2}
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
    false -> {{hole, false}, C1}
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

infer_option(Option, T, FVs, SigVs, C) ->
  {option, Loc, {con_token, _, Con}, ArgTEs, _} = Option,
  {ArgTs, C1} = lists:mapfoldl(fun(ArgTE, FoldC) ->
    infer_sig({T, FVs}, false, FoldC#ctx.sig_vs, ArgTE, FoldC)
  end, C#ctx{sig_vs=SigVs}, ArgTEs),

  RawOptionT = case length(ArgTs) of
    0 -> T;
    _ -> {lam, ArgTs, T}
  end,
  % don't need to make any Vs rigid; inst still works correctly
  {OptionT, _} = norm_sig_type(RawOptionT, false, C1#ctx.pid),
  #binding{tv=TV, id=ID} = g_env_get(Con, C1),

  C2 = new_gnr(TV, ID, C1),
  C3 = add_cst(TV, OptionT, Loc, ?FROM_ENUM_CTOR, C2),
  {OptionT, ArgTs, finish_gnr(C3, C1#ctx.gnr)}.

infer_pattern({var, Loc, Name}=Pattern, {fn, _, _, _, _}=Expr, From, C) ->
  {TV, ID} = tv_server:fresh_gnr_id(C#ctx.pid),
  C1 = l_env_add(Name, #binding{tv=TV, id=ID}, C),
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

  {Vs, C1} = ordsets:fold(fun(Name, {FoldVs, FoldC}) ->
    TV = tv_server:fresh(C#ctx.pid),
    {tv, V, _, _} = TV,
    {[V | FoldVs], l_env_add(Name, #binding{tv=TV, id=ID}, FoldC)}
  end, {[], C}, Names),

  C1#ctx{gnr=C1#ctx.gnr#gnr{vs=Vs}}.

pattern_names([]) -> ordsets:new();
pattern_names([Node | Rest]) ->
  ordsets:union(pattern_names(Node), pattern_names(Rest));
pattern_names({N, _, _}) when N == int; N == float; N == bool; N == char;
    N == str; N == atom; N == var_value ->
  ordsets:new();
pattern_names({var, _, Name}) -> ordsets:from_list([Name]);
pattern_names({N, _}) when N == unit; N == '_' -> ordsets:new();
pattern_names({field, _, ModuleConToken, ConToken}) ->
  ordsets:union(pattern_names(ModuleConToken), pattern_names(ConToken));
pattern_names({variant, _, _, Args}) -> pattern_names(Args);
pattern_names({list, _, Elems}) -> pattern_names(Elems);
pattern_names({cons, _, Elems, Tail}) ->
  ordsets:union(pattern_names(Elems), pattern_names(Tail));
pattern_names({tuple, _, Elems}) -> pattern_names(Elems).

lookup(Name, Loc, C) ->
  case maps:find(Name, C#ctx.l_env) of
    {ok, B} -> {B, C};
    error ->
      case maps:find({C#ctx.module, Name}, C#ctx.g_env) of
        {ok, B} -> {B, C};
        error ->
          TV = tv_server:fresh(C#ctx.pid),
          {#binding{tv=TV}, add_ctx_err(?ERR_NOT_DEF(Name), Loc, C)}
      end
  end.

lookup(Module, Name, Loc, C) ->
  External = C#ctx.module /= Module,

  case maps:find({Module, Name}, C#ctx.g_env) of
    {ok, #binding{exported=false}=B} when External ->
      {B, add_ctx_err(?ERR_NOT_EXPORTED(Name, Module), Loc, C)};
    {ok, B} -> {B, C};

    error ->
      TV = tv_server:fresh(C#ctx.pid),
      C1 = add_ctx_err(?ERR_NOT_DEF(Name, Module), Loc, C),
      {#binding{tv=TV}, C1}
  end.

lookup_inst(Name, Loc, Ref, C) ->
  {B, C1} = lookup(Name, Loc, C),
  binding_inst(B, Name, Loc, Ref, C1).

lookup_inst(Module, Name, Loc, Ref, C) ->
  {B, C1} = lookup(Module, Name, Loc, C),
  binding_inst(B, Name, Loc, Ref, C1).

binding_inst(B, Name, Loc, Ref, C) ->
  case B of
    #binding{tv=TV, id=undefined} -> {TV, C};
    #binding{tv=TV, id=ID} ->
      C1 = C#ctx{gnr=add_gnr_dep(ID, C#ctx.gnr)},

      % We don't want to return {inst, ...} directly; if it's added to two
      % separate constraints, that will cause two separate instantiations.
      % Additionally, we want all returned types to be fully resolved in case
      % they're associated with a reference. To accomplish this, introduce an
      % intermediate TV that will get assigned the inst.
      InstTV = tv_server:fresh(C1#ctx.pid),
      C2 = add_cst(InstTV, {inst, Ref, TV}, Loc, ?FROM_VAR(Name), C1),

      % We need to defer instantiation until we start solving constraints.
      % Otherwise, we don't know the real types of these variables, and can't
      % instantiate properly.
      {InstTV, C2}
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

    case ordsets:is_element(Name, Names) of
      true ->
        {Names, add_ctx_err(?ERR_DUP_FIELD_IMPL(Name), VarLoc, FoldC)};

      false ->
        NewNames = ordsets:add_element(Name, Names),
        NewC = case maps:find(Name, FieldLocTs) of
          error ->
            add_ctx_err(?ERR_EXTRA_FIELD_IMPL(Name, IfaceCon), VarLoc, FoldC);

          {ok, {_FieldLoc, RawFieldT}} ->
            % Remove ifaces on T so we can unify with a gen.
            NoIsOpts = #sub_opts{subs=#{"T" => {set_ifaces, none}}},
            RawNoIs = utils:subs(RawFieldT, NoIsOpts),

            % Don't make anything rigid yet. We still need to unify with a gen
            % that has a concrete base type. Rigidity will come naturally
            % during generalization.
            {FlexSigT, NormSubs} = norm_sig_type(RawNoIs, true, FoldC#ctx.pid),

            NewTV = case maps:find("T", NormSubs) of
              {ok, NewV} -> {tv, NewV, none, false};
              % Could happen if the interface FieldT is invalid and doesn't
              % contain T.
              error -> tv_server:fresh(FoldC#ctx.pid)
            end,

            {SigTV, ID} = tv_server:fresh_gnr_id(FoldC#ctx.pid),
            FoldC1 = new_gnr(SigTV, ID, FoldC),
            FoldC2 = add_cst(SigTV, FlexSigT, ImplLoc, ?FROM_IMPL_TYPE, FoldC1),

            FoldC3 = case IfaceNumParams of
              0 -> add_cst(NewTV, ImplT, ImplLoc, ?FROM_IMPL_TYPE, FoldC2);

              _ ->
                CaseC = add_gen_vs(FlexSigT, FoldC2),
                GenV = tv_server:next_name(CaseC#ctx.pid),

                GenTVParamTs = lists:map(fun(_) ->
                  tv_server:fresh(CaseC#ctx.pid)
                end, lists:seq(1, IfaceNumParams)),
                GenTV = {gen, GenV, none, NewTV, GenTVParamTs},

                Types = CaseC#ctx.types,
                {con, ImplCon} = ImplT,
                #type_binding{num_params=NumParams} = maps:get(ImplCon, Types),

                ParamTs = if
                  IfaceNumParams > 1 andalso NumParams == 1 ->
                    [{tuple, [unit || _ <- lists:seq(1, IfaceNumParams)]}];
                  true -> [unit || _ <- lists:seq(1, NumParams)]
                end,

                GenT = {gen, ImplT, ParamTs},
                add_cst(GenTV, GenT, ImplLoc, ?FROM_IMPL_TYPE, CaseC)
            end,

            FoldC4 = finish_gnr(FoldC3, FoldC#ctx.gnr),

            % All IVs within ImplT will be in the environment during code gen.
            % To make sure they're treated as bound variables, whose impls
            % shouldn't be passed to the Expr here, we add ImplT in the env
            % under some fake variable name.
            FoldC5 = new_gnr(l_env_add("_@Impl", #binding{tv=ImplT}, FoldC4)),

            % Must add SigTV gnr as a dependency so it's solved first.
            FoldC6 = FoldC5#ctx{gnr=add_gnr_dep(ID, FoldC5#ctx.gnr)},
            {ExprT, FoldC7} = infer(Expr, FoldC6),

            TV = tv_server:fresh(FoldC7#ctx.pid),
            % From doesn't really matter; this cst is always inferred first, so
            % it'll never fail.
            ExprCst = make_cst(
              TV,
              ExprT,
              ?LOC(Expr),
              ?FROM_GLOBAL_DEF(Name),
              FoldC7
            ),
            SigCst = make_cst(
              TV,
              SigTV,
              VarLoc,
              ?FROM_IFACE_SIG(IfaceCon),
              FoldC7
            ),

            % Infer ExprCst first, as inference is in reverse order.
            FoldC8 = append_csts([SigCst, ExprCst], FoldC7),
            % Must add the SigTV gnr as a dependency so it gets solved first.
            FoldC9 = finish_gnr(FoldC8, FoldC4#ctx.gnr),
            FoldC9#ctx{l_env=FoldC4#ctx.l_env}
        end,

        {NewNames, NewC}
    end
  end, {ordsets:new(), C}, Inits).

g_env_get(Name, #ctx{module=Module, g_env=GEnv}) ->
  maps:get({Module, Name}, GEnv).

l_env_add(Name, B, #ctx{l_env=LEnv}=C) -> C#ctx{l_env=LEnv#{Name => B}}.

new_gnr(C) ->
  ID = tv_server:next_gnr_id(C#ctx.pid),
  G = #gnr{id=ID, vs=[], l_env=C#ctx.l_env, csts=[], deps=ordsets:new()},
  C#ctx{gnr=G}.

new_gnr({tv, V, _, _}, ID, C) ->
  G = #gnr{id=ID, vs=[V], l_env=C#ctx.l_env, csts=[], deps=ordsets:new()},
  C#ctx{gnr=G}.

finish_gnr(C, OldG) -> C#ctx{gnrs=[C#ctx.gnr | C#ctx.gnrs], gnr=OldG}.

add_gnr_dep(ID, G) -> G#gnr{deps=ordsets:add_element(ID, G#gnr.deps)}.

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
    {ok, #type_binding{is_iface=IsIface, num_params=NumParams}} -> C;

    {ok, #type_binding{is_iface=false}} when IsIface ->
      add_ctx_err(?ERR_TYPE_NOT_IFACE(Con), Loc, C);
    {ok, #type_binding{is_iface=true}} when not IsIface ->
      add_ctx_err(?ERR_IFACE_NOT_TYPE(Con), Loc, C);

    {ok, #type_binding{num_params=ExpNumParams}} ->
      Msg = ?ERR_TYPE_PARAMS(Con, ExpNumParams, NumParams),
      add_ctx_err(Msg, Loc, C);

    % TODO: better messages when module is not defined (e.g. Bad.Type) and
    % module is defined but no such type exists (e.g. Module.Bad)
    error when IsIface -> add_ctx_err(?ERR_NOT_DEF_IFACE(Con), Loc, C);
    error when not IsIface -> add_ctx_err(?ERR_NOT_DEF_TYPE(Con), Loc, C)
  end.

add_ctx_err(Msg, Loc, C) ->
  C#ctx{errs=[{Msg, C#ctx.module, Loc} | C#ctx.errs]}.

no_ctx_errs(C1, C2) -> length(C1#ctx.errs) == length(C2#ctx.errs).

add_alias(Con, Vs, T, IsStruct, C) ->
  C#ctx{aliases=(C#ctx.aliases)#{Con => {Vs, T, IsStruct}}}.

norm_sig_type(SigT, Inst, Pid) ->
  TVsList = utils:tvs_list(SigT),

  Subs = lists:foldl(fun(T, FoldSubs) ->
    NewV = tv_server:next_name(Pid),

    MakeRigid = case T of
      {tv, V, _, true} -> not Inst;

      % Non-rigid TVs in a signature are caused by errors in infer_sig(), and
      % should not be made rigid.
      {tv, V, _, false} -> false;

      % Gen TVs are newly generated during each call to infer_sig(), but we
      % still need to normalize them because the same signature may be passed
      % through norm_sig_type() multiple times, and we must ensure each time
      % produces a new, independent type.
      {gen, V, _, _, _} -> not Inst
    end,

    case MakeRigid of
      true -> FoldSubs#{V => {rigid, NewV}};
      false -> FoldSubs#{V => NewV}
    end
  end, #{}, TVsList),

  % type sigs don't need consolidation, so don't pass aliases
  {utils:subs(SigT, #sub_opts{subs=Subs, shallow=true}), Subs}.

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
    passed_vs=PassedVs,
    return_vs=ReturnVs,
    must_solve_vs=MustSolveVs,
    err_vs=ErrVs
  }=S1 = T#tarjan.solver,

  SubbedMustSolveVs = ordsets:fold(fun(V, FoldMustSolveVs) ->
    % Is and Rigid don't matter for subs.
    case subs_s({tv, V, none, false}, S1) of
      % Rigidity doesn't matter; if NewV is rigid, it should still be solved
      % for by means of a bound impl.
      {tv, NewV, _, _} -> ordsets:add_element(NewV, FoldMustSolveVs);
      {gen, NewV, _, _, _} -> ordsets:add_element(NewV, FoldMustSolveVs);
      _ -> FoldMustSolveVs
    end
  end, ordsets:new(), MustSolveVs),

  SubbedErrVs = ordsets:fold(fun(ErrV, FoldErrVs) ->
    % Is and Rigid don't matter for subs.
    case subs_s({tv, ErrV, none, false}, S1) of
      % Rigidity doesn't matter; we tried to unify ErrV/NewV with a concrete
      % type at some point, so don't report ambiguity error until the user
      % decides which it actually is.
      {tv, NewV, _, _} -> ordsets:add_element(NewV, FoldErrVs);
      {gen, NewV, _, _, _} -> ordsets:add_element(NewV, FoldErrVs);
      _ -> FoldErrVs
    end
  end, ordsets:new(), ErrVs),

  {ReportedVs, S2} = lists:foldl(fun(PassedV, {FoldReportedVs, FoldS}) ->
    {OrigV, ArgT, Module, Loc, LEnv} = PassedV,
    % Is and Rigid don't matter for subs.
    SubbedT = subs_s({tv, OrigV, none, false}, FoldS),
    BoundVs = bound_vs(LEnv, FoldS),

    ordsets:fold(fun(V, {NestedReportedVs, NestedS}) ->
      validate_solved(
        {V, ArgT, Module, Loc, LEnv},
        true,
        SubbedMustSolveVs,
        SubbedErrVs,
        BoundVs,
        NestedReportedVs,
        NestedS
      )
    end, {FoldReportedVs, FoldS}, fvs(SubbedT))
  end, {ordsets:new(), S1}, PassedVs),

  {_, FinalS} = lists:foldl(fun(ReturnV, {FoldReportedVs, FoldS}) ->
    {_, _, _, _, LEnv} = ReturnV,
    BoundVs = bound_vs(LEnv, FoldS),
    validate_solved(
      ReturnV,
      false,
      SubbedMustSolveVs,
      SubbedErrVs,
      BoundVs,
      FoldReportedVs,
      FoldS
    )
  end, {ReportedVs, S2}, ReturnVs),

  case FinalS#solver.errs of
    [] -> {ok, FinalS};

    Errs ->
      SubbedErrs = lists:map(fun({Msg, Module, Loc}) ->
        NewMsg = lists:map(fun
          (ErrT) when is_tuple(ErrT) orelse ErrT == unit ->
            subs_s(ErrT, FinalS, #sub_opts{for_err=true});
          (Part) -> Part
        end, Msg),
        {NewMsg, Module, Loc}
      end, Errs),

      {errors, SubbedErrs}
  end.

validate_solved(
  {V, T, Module, Loc, _},
  IsArg,
  MustSolveVs,
  ErrVs,
  BoundVs,
  ReportedVs,
  S
) ->
  MustSolveV = ordsets:is_element(V, MustSolveVs),
  IsErrV = ordsets:is_element(V, ErrVs),
  Bound = ordsets:is_element(V, BoundVs),
  Reported = ordsets:is_element(V, ReportedVs),

  if
    MustSolveV, not IsErrV, not Bound, not Reported ->
      SubbedT = subs_s(T, S),
      GenTV = lists:foldl(fun({_, GenTV}, FoldGenTV) ->
        {gen, HiddenV, _, _, _} = GenTV,
        case {HiddenV, FoldGenTV} of
          {V, none} -> GenTV;
          _ -> FoldGenTV
        end
      end, none, gen_vs_list(SubbedT)),

      MustSolveT = case GenTV of
        none ->
          {Is, _} = lists:keyfind(V, 2, utils:all_ivs(SubbedT)),
          {tv, V, Is, false};
        _ -> GenTV
      end,

      Msg = if
        IsArg -> ?ERR_MUST_SOLVE_ARG(SubbedT, MustSolveT);
        true -> ?ERR_MUST_SOLVE_RETURN(SubbedT, MustSolveT)
      end,

      NewErrs = [{Msg, Module, Loc} | S#solver.errs],
      NewReportedVs = ordsets:add_element(V, ReportedVs),
      {NewReportedVs, S#solver{errs=NewErrs}};

    true -> {ReportedVs, S}
  end.

connect(ID, #tarjan{stack=Stack, map=Map, next_index=NextIndex, solver=S}) ->
  #{ID := G} = Map,
  Stack1 = [ID | Stack],
  Map1 = Map#{ID := G#gnr{index=NextIndex, low_link=NextIndex, on_stack=true}},

  T1 = #tarjan{stack=Stack1, map=Map1, next_index=NextIndex + 1, solver=S},
  T2 = ordsets:fold(fun(AdjID, FoldT) ->
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
        BoundVs = bound_vs(SolG#gnr.l_env, FoldS),

        lists:foldl(fun(SolV, NestedS) ->
          SolTV = {tv, SolV, none, false},
          T = subs_s(SolTV, NestedS),

          GVs = ordsets:subtract(fvs(T), BoundVs),
          NestedS1 = lists:foldl(fun
            ({tv, V, _, false}, DeepS) ->
              case ordsets:is_element(V, GVs) of
                true ->
                  case maps:find(V, DeepS#solver.subs) of
                    {ok, {set_ifaces, Is}} ->
                      {_, DeepS1} = add_sub(V, {set_ifaces_rigid, Is}, DeepS),
                      DeepS1;
                    error ->
                      {_, DeepS1} = add_sub(V, {rigid, V}, DeepS),
                      DeepS1;

                    % Either of these occur if we loop over the same V twice.
                    {ok, {rigid, V}} -> DeepS;
                    {ok, {set_ifaces_rigid, _}} -> DeepS
                  end;

                false -> DeepS
              end;

            (_, DeepS) -> DeepS
          end, NestedS, utils:tvs_list(T)),

          #solver{schemes=Schemes} = NestedS1,
          Scheme = {GVs, subs_s(T, NestedS1), ordsets:subtract(fvs(T), GVs)},
          Schemes1 = Schemes#{SolV => Scheme},
          NestedS1#solver{schemes=Schemes1}
        end, FoldS, SolG#gnr.vs)
      end, S3, SolvableIDs),

      T2#tarjan{stack=tl(Left), map=Map3, solver=S4};

    true -> T2
  end.

unify_csts(#gnr{csts=Csts, l_env=LEnv}, S) ->
  BoundVs = bound_vs(LEnv, S),

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

    {_, FoldS4} = unify(SubbedT1, SubbedT2, FoldS3),
    FoldS4
  end, S#solver{bound_vs=BoundVs, l_env=LEnv}, Csts).

resolve({lam, ArgTs, ReturnT}, S) ->
  {ResArgTs, S1} = lists:mapfoldl(fun(ArgT, FoldS) ->
    resolve(ArgT, FoldS)
  end, S, ArgTs),
  {ResReturnT, S2} = resolve(ReturnT, S1),
  {{lam, ResArgTs, ResReturnT}, S2};
resolve({lam, LEnv, Provided, ReturnT}, S) ->
  {ResProvided, S1} = lists:mapfoldl(fun({Type, Loc, ArgT}, FoldS) ->
    {ResArgT, FoldS1} = resolve(ArgT, FoldS),
    {{Type, Loc, ResArgT}, FoldS1}
  end, S, Provided),
  {ResReturnT, S2} = resolve(ReturnT, S1),
  {{lam, LEnv, ResProvided, ResReturnT}, S2};
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
  case maps:find(InstV, S#solver.schemes) of
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
      NewInstRefs = InstRefs#{Ref => {deferred, TV, S#solver.l_env}},
      resolve(TV, S#solver{inst_refs=NewInstRefs});

    {ok, {GVs, T, _}} -> resolve({inst, Ref, GVs, T}, S)
  end;
resolve({inst, Ref, GVs, T}, #solver{inst_refs=InstRefs}=S) ->
  InstT = inst(GVs, T, S#solver.pid),
  S1 = case Ref of
    none -> S;
    _ ->
      % Every V of T that can be generalized won't be in InstT. Only bound,
      % non-generalizable Vs will remain, which shouldn't be in SubbedVs.
      IVs = utils:ivs(InstT, fvs(T)),
      #solver{iv_origins=IVOrigins} = S,

      case IVs of
        [] -> S;
        _ ->
          SubbedVs = add_subbed_vs(IVs, #{}),
          NewIVOrigins = lists:foldl(fun({Is, V}, FoldIVOrigins) ->
            Origins = ordsets:from_list([{Ref, V}]),

            ordsets:fold(fun(I, NestedIVOrigins) ->
              NestedIVOrigins#{{I, V} => Origins}
            end, FoldIVOrigins, Is)
          end, IVOrigins, IVs),

          S#solver{
            inst_refs=InstRefs#{Ref => {InstT, SubbedVs}},
            iv_origins=NewIVOrigins
          }
      end
  end,

  resolve(InstT, add_gen_vs(InstT, S1));
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
resolve({hole, Report}, S) -> {{hole, Report}, S};
resolve(unit, S) -> {unit, S}.

inst(GVs, T, Pid) ->
  Subs = ordsets:fold(fun(V, FoldSubs) ->
    FoldSubs#{V => tv_server:next_name(Pid)}
  end, #{}, GVs),
  % consolidation already happened when finalizing scheme; no aliases needed
  utils:subs(T, #sub_opts{subs=Subs}).

unify(T1, T2, S) when T1 == T2 -> {true, S};

% Always return false when there's a hole, as this indicates that we can't
% unify successfully.
unify({hole, false}, _, S) -> {false, S};
unify({hole, true}, T, S) -> add_err(?ERR_HOLE(T), S);
unify(T1, {hole, _}=T2, S) -> sub_unify(T2, T1, S);

unify({lam, ArgTs1, ReturnT1}, {lam, ArgTs2, ReturnT2}, S) ->
  if
    length(ArgTs1) /= length(ArgTs2) -> add_err(S);
    true ->
      {ArgsValid, S1} = lists:foldl(fun({T1, T2}, {FoldValid, FoldS}) ->
        {ArgValid, FoldS1} = sub_unify(T1, T2, FoldS),
        {FoldValid andalso ArgValid, FoldS1}
      end, {true, S}, lists:zip(ArgTs1, ArgTs2)),
      {ReturnValid, S2} = sub_unify(ReturnT1, ReturnT2, S1),
      {ArgsValid andalso ReturnValid, S2}
  end;
unify({lam, _, Provided, _}, {lam, ArgTs, _}, S)
    when length(Provided) /= length(ArgTs) ->
  add_err(?ERR_ARITY(length(Provided), length(ArgTs)), S);
unify({lam, LEnv, Provided, ReturnT1}, {lam, ArgTs, ReturnT2}, S) ->
  #solver{
    module=Module,
    loc=OrigLoc,
    t1=OrigT1,
    t2=OrigT2,
    passed_vs=PassedVs,
    return_vs=ReturnVs,
    must_solve_vs=MustSolveVs
  } = S,

  ProvidedArgTs = lists:zip(Provided, ArgTs),
  {NewPassedVs, HasHole} = lists:foldl(fun
    % The user isn't actually passing an argument if there's a hole.
    ({{hole, _, _}, _}, {FoldPassedVs, _}) -> {FoldPassedVs, true};
    ({{arg, Loc, _}, ArgT}, {FoldPassedVs, FoldHasHole}) ->
      NewPassedVs = ordsets:fold(fun(V, NestedPassedVs) ->
        [{V, ArgT, Module, Loc, LEnv} | NestedPassedVs]
      end, FoldPassedVs, fvs(ArgT)),
      {NewPassedVs, FoldHasHole}
  end, {PassedVs, false}, ProvidedArgTs),

  VsWithIs = lists:flatmap(fun
    ({{hole, _, _}, _}) -> [];
    ({_, ArgT}) -> [V || {_, V} <- utils:ivs(ArgT)]
  end, ProvidedArgTs),
  ReturnVsWithIs = if
    % Args are still left; we shouldn't add any ReturnVs or MustSolveVs.
    HasHole -> [];
    true -> lists:map(fun({_, V}) -> V end, utils:ivs(ReturnT2))
  end,

  NewMustSolveVs = ordsets:union([
    MustSolveVs,
    ordsets:from_list(VsWithIs),
    ordsets:from_list(ReturnVsWithIs)
  ]),
  NewReturnVs = lists:foldl(fun(V, FoldReturnVs) ->
    % Use OrigLoc, which spans the entire app, to represent the return type.
    [{V, ReturnT2, Module, OrigLoc, LEnv} | FoldReturnVs]
  end, ReturnVs, ReturnVsWithIs),

  S1 = S#solver{
    passed_vs=NewPassedVs,
    return_vs=NewReturnVs,
    must_solve_vs=NewMustSolveVs
  },

  {ArgsValid, S2} = lists:foldl(fun({{_, Loc, GivenT}, ArgT}, Memo) ->
    {FoldValid, FoldS} = Memo,
    FoldS1 = FoldS#solver{loc=Loc, t1=GivenT, t2=ArgT},
    {ArgValid, FoldS2} = sub_unify(GivenT, ArgT, FoldS1),
    {FoldValid andalso ArgValid, FoldS2}
  end, {true, S1}, ProvidedArgTs),

  % We're done with the arguments of the function application. We shouldn't
  % include the full lam types in errors between the return types (not only
  % is it confusing to the user, but it'll also be misreported as an arity
  % error), so set the return types to be t1/t2.
  S3 = S2#solver{loc=OrigLoc, t1=ReturnT1, t2=ReturnT2},
  {ReturnValid, S4} = sub_unify(ReturnT1, ReturnT2, S3),
  {ArgsValid andalso ReturnValid, S4#solver{t1=OrigT1, t2=OrigT2}};
unify({lam, _, _}=T1, {lam, _, _, _}=T2, S) -> sub_unify(T2, T1, S);

unify({tuple, ElemTs1}, {tuple, ElemTs2}, S) ->
  if
    length(ElemTs1) /= length(ElemTs2) -> add_err(S);
    true ->
      lists:foldl(fun({T1, T2}, {FoldValid, FoldS}) ->
        {ElemValid, FoldS1} = sub_unify(T1, T2, FoldS),
        {FoldValid andalso ElemValid, FoldS1}
      end, {true, S}, lists:zip(ElemTs1, ElemTs2))
  end;

unify({record, A1, FieldMap1}, {record, A2, FieldMap2}, S) ->
  Keys1 = ordsets:from_list(maps:keys(FieldMap1)),
  Keys2 = ordsets:from_list(maps:keys(FieldMap2)),

  if
    Keys1 /= Keys2 -> add_err(S);
    true ->
      {Valid, S1} = ordsets:fold(fun(Key, {FoldValid, FoldS}) ->
        {FieldValid, FoldS1} = sub_unify(
          maps:get(Key, FieldMap1),
          maps:get(Key, FieldMap2),
          FoldS
        ),
        {FoldValid andalso FieldValid, FoldS1}
      end, {true, S}, Keys1),

      if
        Valid -> add_sub_anchor(A1, A2, S1);
        true -> {false, S1}
      end
  end;

unify({record, A1, FieldMap}, {record_ext, A2, BaseT, Ext}, S) ->
  Keys = ordsets:from_list(maps:keys(FieldMap)),
  KeysExt = ordsets:from_list(maps:keys(Ext)),

  case ordsets:is_subset(KeysExt, Keys) of
    true ->
      {MapValid, S1} = ordsets:fold(fun(Key, {FoldValid, FoldS}) ->
        {FieldValid, FoldS1} = sub_unify(
          maps:get(Key, FieldMap),
          maps:get(Key, Ext),
          FoldS
        ),
        {FoldValid andalso FieldValid, FoldS1}
      end, {true, S}, KeysExt),

      RelaxedFieldMap = ordsets:fold(fun(Key, FoldFieldMap) ->
        TV = tv_server:fresh(S#solver.pid),
        FoldFieldMap#{Key => TV}
      end, FieldMap, KeysExt),

      NewA = tv_server:next_name(S1#solver.pid),
      {BaseValid, S2} = sub_unify(BaseT, {record, NewA, RelaxedFieldMap}, S1),

      if
        MapValid, BaseValid -> add_sub_anchor(A1, A2, S2);
        true -> {false, S2}
      end;

    false -> add_err(S)
  end;
unify({record_ext, _, _, _}=T1, {record, _, _}=T2, S) ->
  sub_unify(T2, T1, S);

unify({record_ext, A1, BaseT1, Ext1}, {record_ext, A2, BaseT2, Ext2}, S) ->
  Keys1 = ordsets:from_list(maps:keys(Ext1)),
  Keys2 = ordsets:from_list(maps:keys(Ext2)),
  CommonKeys = ordsets:intersection(Keys1, Keys2),

  {RelaxedExt1, RelaxedExt2, ExtValid, S1} = ordsets:fold(fun(Key, Memo) ->
    {FoldExt1, FoldExt2, FoldValid, FoldS} = Memo,
    NewFoldExt1 = maps:remove(Key, FoldExt1),
    NewFoldExt2 = maps:remove(Key, FoldExt2),

    {FieldValid, NewFoldS} = sub_unify(
      maps:get(Key, Ext1),
      maps:get(Key, Ext2),
      FoldS
    ),
    {NewFoldExt1, NewFoldExt2, FoldValid andalso FieldValid, NewFoldS}
  end, {Ext1, Ext2, true, S}, CommonKeys),

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
  {Base1Valid, S2} = case maps:size(RelaxedExt2) of
    0 -> {true, S1};
    _ ->
      NewA1 = tv_server:next_name(S#solver.pid),
      TV1 = tv_server:fresh(S#solver.pid),
      sub_unify(BaseT1, {record_ext, NewA1, TV1, RelaxedExt2}, S1)
  end,

  {Base2Valid, S3} = case maps:size(RelaxedExt1) of
    0 -> {true, S2};
    _ ->
      NewA2 = tv_server:next_name(S#solver.pid),
      TV2 = tv_server:fresh(S#solver.pid),
      sub_unify(BaseT2, {record_ext, NewA2, TV2, RelaxedExt1}, S2)
  end,

  if
    ExtValid, Base1Valid, Base2Valid -> add_sub_anchor(A1, A2, S3);
    true -> {false, S3}
  end;

% If BaseT is *not* a TV, then this gen TV should've been replaced with
% a regular gen. It hasn't been replaced due to a unification error. Avoid
% propagating errors.
unify({gen, _, _, BaseT, _}, _, S) when element(1, BaseT) /= tv -> {false, S};
unify(_, {gen, _, _, BaseT, _}, S) when element(1, BaseT) /= tv -> {false, S};

unify({tv, V1, Is1, Rigid1}=TV1, {tv, V2, Is2, Rigid2}=TV2, S) ->
  #solver{bound_vs=BoundVs, ifaces=Ifaces} = S,
  Bound1 = ordsets:is_element(V1, BoundVs),
  Bound2 = ordsets:is_element(V2, BoundVs),
  Occurs = occurs(V1, TV2) or occurs(V2, TV1),

  if
    Occurs -> add_err(S);
    Rigid1, Rigid2 -> add_rigid_err(?ERR_RIGID_RIGID(TV1, TV2), S);

    Rigid1 ->
      if
        Bound2 -> add_rigid_err(?ERR_RIGID_BOUND(TV1, TV2), S);
        true ->
          case merge_is(Is1, Is2, Ifaces) == Is1 of
            true -> add_sub(V2, TV1, S);
            false -> add_rigid_err(?ERR_RIGID_TV(TV1, TV2), S)
          end
      end;

    Rigid2 ->
      if
        Bound1 -> add_rigid_err(?ERR_RIGID_BOUND(TV2, TV1), S);
        true ->
          case merge_is(Is1, Is2, Ifaces) == Is2 of
            true -> add_sub(V1, TV2, S);
            false -> add_rigid_err(?ERR_RIGID_TV(TV2, TV1), S)
          end
      end;

    true ->
      GenVs = S#solver.gen_vs,
      NewGenVs = case {maps:find(V1, GenVs), maps:find(V2, GenVs)} of
        {error, error} -> GenVs;
        {{ok, GenTVs}, error} -> GenVs#{V2 => GenTVs};
        {error, {ok, GenTVs}} -> GenVs#{V1 => GenTVs};
        {{ok, GenTVs1}, {ok, GenTVs2}} ->
          MergedGenTVs = GenTVs1 ++ GenTVs2,
          GenVs#{V1 => MergedGenTVs, V2 => MergedGenTVs}
      end,
      CaseS = S#solver{gen_vs=NewGenVs},

      if
        Is1 == none -> add_sub(V1, TV2, CaseS);
        Is2 == none -> add_sub(V2, TV1, CaseS);
        true ->
          MergedSub = {set_ifaces, merge_is(Is1, Is2, Ifaces)},
          {_, CaseS1} = add_sub(V2, TV1, CaseS),
          {_, CaseS2} = add_sub(V1, MergedSub, CaseS1),
          {true, merge_iv_origins(Is2, V2, V1, CaseS2)}
      end
  end;

unify({tv, V, Is, Rigid}=TV, T, #solver{bound_vs=BoundVs}=S) ->
  Occurs = occurs(V, T),
  Bound = ordsets:is_element(V, BoundVs),
  WouldEscape = Bound and occurs(true, T),

  {Valid, S1} = if
    Rigid -> add_rigid_err(?ERR_RIGID_CON(TV), S);
    Occurs -> add_err(S);

    WouldEscape ->
      [RigidTV | _] = lists:filter(fun
        ({tv, _, _, true}) -> true;
        (_) -> false
      end, utils:tvs_list(T)),
      add_rigid_err(?ERR_RIGID_BOUND(RigidTV, TV), S);

    true ->
      case {T, Is} of
        % V can sub with anything, so just sub V with GenTV below
        {_, none} -> {true, S};

        % same interfaces, so just sub V with GenTV below
        {{gen, _, Is, _, _}, _} -> {true, S};

        % different interfaces and GenTV is rigid, so fail
        {{gen, _, _, {tv, _, _, true}, _}=GenTV, _} ->
          add_rigid_err(?ERR_RIGID_TV(GenTV, TV), S);

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
          MergedSub = {set_ifaces, merge_is(Is, Is1, S#solver.ifaces)},
          {_, CaseS} = add_sub(V1, MergedSub, S),
          {true, merge_iv_origins(Is, V, V1, CaseS)};

        _ ->
          ordsets:fold(fun(I, {FoldValid, FoldS}) ->
            {ValidInst, FoldS1} = instance(T, I, V, FoldS),
            {FoldValid andalso ValidInst, FoldS1}
          end, {true, S}, Is)
      end
  end,

  if
    Valid -> add_sub(V, T, S1);

    % There was an attempt to unify V with a concrete type; avoid reporting
    % ambiguity errors. It's possible that T is a gen TV, which isn't a concrete
    % type, but we find that still adding an ErrV results in fewer, more
    % relevant messages (if the gen TV is bound, but V isn't, then we'll get
    % a spurious ambiguity error if we don't add an ErrV).
    true -> add_err_v(V, S1)
  end;
unify(T, {tv, V, Is, Rigid}, S) -> sub_unify({tv, V, Is, Rigid}, T, S);

unify({gen, {con, Con}, ParamTs1}, {gen, {con, Con}, ParamTs2}, S) ->
  if
    length(ParamTs1) /= length(ParamTs2) -> add_err(S);
    true ->
      lists:foldl(fun({T1, T2}, {FoldValid, FoldS}) ->
        {ParamValid, FoldS1} = sub_unify(T1, T2, FoldS),
        {FoldValid andalso ParamValid, FoldS1}
      end, {true, S}, lists:zip(ParamTs1, ParamTs2))
  end;

unify({gen, ConT, ParamTs1}=GenT, {gen, V, Is, BaseTV, ParamTs2}=GenTV, S) ->
  Length1 = length(ParamTs1),
  Length2 = length(ParamTs2),

  {ParamsValid, S1} = if
    Length1 == Length2 ->
      lists:foldl(fun({T1, T2}, {FoldValid, FoldS}) ->
        {ParamValid, FoldS1} = sub_unify(T1, T2, FoldS),
        {FoldValid andalso ParamValid, FoldS1}
      end, {true, S}, lists:zip(ParamTs1, ParamTs2));

    Length1 == 1 ->
      case ParamTs1 of
        [{tv, _, _, _}=ParamT] ->
          sub_unify(ParamT, {tuple, ParamTs2}, S);
        [{tuple, Elems}=ParamT] when length(Elems) == Length2 ->
          sub_unify(ParamT, {tuple, ParamTs2}, S);
        _ -> add_err(S)
      end;

    Length2 == 1 ->
      case ParamTs2 of
        [{tv, _, _, _}] -> {true, S};
        [{tuple, Elems}] when length(Elems) == Length1 -> {true, S};
        _ -> add_err(S)
      end;

    true -> add_err(S)
  end,

  if
    ParamsValid ->
      {BaseValid, S2} = sub_unify(BaseTV, ConT, S1),
      if
        BaseValid ->
          {GenValid, S3} = sub_unify_gen_vs(GenTV, ConT, Length1, S2),
          if
            GenValid -> sub_unify({tv, V, Is, false}, GenT, S3);
            true -> {false, S3}
          end;

        true -> {false, S2}
      end;

    true -> {false, S1}
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

  {ParamsValid, S1} = if
    SameLengths ->
      lists:foldl(fun({T1, T2}, {FoldValid, FoldS}) ->
        {ParamValid, FoldS1} = sub_unify(T1, T2, FoldS),
        {FoldValid andalso ParamValid, FoldS1}
      end, {true, S}, lists:zip(ParamTs1, ParamTs2));

    Length1 == 1 ->
      case ParamTs1 of
        [{tv, _, _, _}] -> {true, S};
        [{tuple, Elems}] when length(Elems) == Length2 -> {true, S};
        _ -> add_err(S)
      end;

    Length2 == 1 ->
      case ParamTs2 of
        [{tv, _, _, _}] -> {true, S};
        [{tuple, Elems}] when length(Elems) == Length1 -> {true, S};
        _ -> add_err(S)
      end;

    true -> add_err(S)
  end,

  if
    ParamsValid ->
      % Do this before unifying BaseTV1 and BaseTV2 so the GenTV sets are
      % merged after params are fixed.
      {GenValid, S2} = if
        not SameLengths andalso Length1 == 1 ->
          sub_unify_gen_vs(GenTV1, none, Length2, S1);
        not SameLengths andalso Length2 == 1 ->
          sub_unify_gen_vs(GenTV2, none, Length1, S1);
        SameLengths -> {true, S1}
      end,

      if
        GenValid ->
          {BaseValid, S3} = sub_unify(BaseTV1, BaseTV2, S2),
          if
            BaseValid ->
              sub_unify({tv, V1, Is1, false}, {tv, V2, Is2, false}, S3);
            true -> {false, S3}
          end;

        true -> {false, S2}
      end;

    true -> {false, S1}
  end;

unify(T1, T2, S) when element(1, T2) == record; element(1, T2) == record_ext ->
  #solver{t1=FullT1, t2=FullT2, aliases=Aliases} = S,
  case utils:unalias(T1, Aliases) of
    T1 -> add_err(S);
    NewT1 ->
      % Show the unaliased FullT1/FullT2 for clarity. We *cannot* assume FullT1
      % is T1 for the following reasons:
      %
      % (a) We may be sub-unifying a part of FullT1, so T1 will be a type
      % contained within FullT1.
      %
      % (b) T1 could actually correspond to FullT2; we don't maintain ordering
      % when calling sub_unify().
      {Valid, S1} = sub_unify(NewT1, T2, S#solver{
        t1=utils:unalias(FullT1, Aliases),
        t2=utils:unalias(FullT2, Aliases)
      }),
      S2 = S1#solver{t1=FullT1, t2=FullT2},

      A = element(2, T2),
      if
        Valid andalso A /= none -> add_sub(A, T1, S2);
        Valid -> {true, S2};
        true -> {false, S2}
      end
  end;
unify(T1, T2, S) when element(1, T1) == record; element(1, T1) == record_ext ->
  sub_unify(T2, T1, S);

unify(T1, T2, #solver{aliases=Aliases}=S) ->
  case {utils:unalias(T1, Aliases), utils:unalias(T2, Aliases)} of
    {T1, T2} -> add_err(S);

    % At least one type was an alias:
    {NewT1, NewT2} ->
      % If we were to unalias S#solver.t1/t2 here, we would never show
      % unification errors between a struct Foo and some other type, since
      % Foo would always get unaliased. Hence, leave t1/t2 as is.
      sub_unify(NewT1, NewT2, S)
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

  {Valid, S1} = lists:foldl(fun(GenTV, {FoldValid, FoldS}) ->
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
    {ParamsValid, FoldS2} = case NewParamTs of
      none -> {true, FoldS1};
      [NewParamT] -> sub_unify(NewParamT, {tuple, FoldParamTs}, FoldS1);
      _ ->
        [FoldParamT] = FoldParamTs,
        sub_unify(FoldParamT, {tuple, NewParamTs}, FoldS1)
    end,

    if
      ParamsValid ->
        {GenValid, FoldS3} = sub_unify(
          {tv, FoldV, FoldIs, false},
          TargetT,
          FoldS2
        ),
        {FoldValid andalso GenValid, FoldS3};
      true -> {false, FoldS2}
    end
  end, {true, S}, GenVs),

  {Valid, S1#solver{t1=OrigT1, t2=OrigT2}}.

merge_is(none, Is2, _) -> Is2;
merge_is(Is1, none, _) -> Is1;
merge_is(Is1, Is2, Ifaces) ->
  Union = ordsets:union(Is1, Is2),
  {MergedIs, _} = ordsets:fold(fun(I, {FoldIs, FoldFamily}) ->
    case ordsets:is_element(I, FoldFamily) of
      true -> {FoldIs, FoldFamily};
      false ->
        NewFamily = utils:family_is(I, Ifaces),
        NewIs = ordsets:filter(fun(ExistingI) ->
          not ordsets:is_element(ExistingI, NewFamily)
        end, FoldIs),
        {ordsets:add_element(I, NewIs), ordsets:union(FoldFamily, NewFamily)}
    end
  end, {ordsets:new(), ordsets:new()}, Union),
  MergedIs.

merge_iv_origins(Is, V, TargetV, S) ->
  IsExceptBuiltin = ordsets:subtract(Is, utils:builtin_is()),
  NewIVOrigins = ordsets:fold(fun(I, FoldIVOrigins) ->
    VOrigins = maps:get({I, V}, FoldIVOrigins),
    case maps:find({I, TargetV}, FoldIVOrigins) of
      {ok, TargetVOrigins} ->
        MergedOrigins = ordsets:union(VOrigins, TargetVOrigins),
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
    {lam, _, Provided, ReturnT} ->
      {lam, [T || {_, _, T} <- Provided], ReturnT};
    _ -> RawSub
  end,

  S1 = case maps:find(V, S#solver.subs) of
    error -> S#solver{subs=(S#solver.subs)#{V => Sub}};
    % we're allowed to override set_ifaces to another value
    {ok, {set_ifaces, _}} -> S#solver{subs=(S#solver.subs)#{V => Sub}};
    {ok, Existing} -> error({badarg, V, Existing, Sub})
  end,

  BoundVs = S1#solver.bound_vs,
  S2 = case {Sub, ordsets:is_element(V, BoundVs)} of
    % No need to update FVs if V isn't in env.
    {_, false} -> S1;
    {_, true} ->
      % Is and Rigid don't matter here, since we're just computing FVs.
      NewFVs = fvs(subs_s({tv, V, none, false}, S1)),
      NewBoundVs = ordsets:union(NewFVs, ordsets:del_element(V, BoundVs)),
      S1#solver{bound_vs=NewBoundVs}
  end,
  {true, S2}.

add_sub_anchor(A1, A2, S) when A1 == none; A2 == none; A1 == A2 -> {true, S};
add_sub_anchor(A1, A2, S) -> add_sub(A2, {anchor, A1}, S).

add_err(S) ->
  #solver{t1=T1, t2=T2, from=From} = S,
  add_err(?ERR_TYPE_MISMATCH(T1, T2, From), S).

add_err(Msg, #solver{module=Module, loc=Loc, errs=Errs}=S) ->
  IsMismatch = hd(Msg) == ?MISMATCH_PREFIX,
  S1 = case Errs of
    % De-duplicate mismatched types errors.
    [{OtherMsg, Module, Loc} | _] when IsMismatch,
      hd(OtherMsg) == ?MISMATCH_PREFIX -> S;

    _ -> S#solver{errs=[{Msg, Module, Loc} | Errs]}
  end,
  {false, S1}.

add_rigid_err(Err, S) ->
  #solver{t1=T1, t2=T2, from=From} = S,
  add_err(rigid_err(T1, T2, From, Err), S).

rigid_err(T1, T2, From, Err) ->
  ?ERR_TYPE_MISMATCH(T1, T2, From) ++ [$., $\s | Err].

add_err_v(V, #solver{err_vs=ErrVs}=S) ->
  {false, S#solver{err_vs=ordsets:add_element(V, ErrVs)}}.

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
      unalias_except_struct(utils:subs(T, Opts), Aliases);
    % no need to unalias ParamTs because we'll recursively unalias them if
    % necessary in infer_sig_helper
    _ -> {gen, {con, Con}, ParamTs}
  end;
unalias_except_struct(T, _) -> T.

instance({con, "Int"}, "Num", _, S) -> {true, S};
instance({con, "Float"}, "Num", _, S) -> {true, S};
instance({con, "Int"}, "Ord", _, S) -> {true, S};
instance({con, "Float"}, "Ord", _, S) -> {true, S};
instance({con, "String"}, "Ord", _, S) -> {true, S};
instance({con, "Char"}, "Ord", _, S) -> {true, S};
instance({con, "String"}, "Concatable", _, S) -> {true, S};
instance({gen, {con, "List"}, _}, "Concatable", _, S) -> {true, S};
instance({gen, {con, "Map"}, _}, "Concatable", _, S) -> {true, S};
instance({gen, {con, "Set"}, _}, "Concatable", _, S) -> {true, S};
instance({gen, {con, "List"}, _}, "Separable", _, S) -> {true, S};
instance({gen, {con, "Set"}, _}, "Separable", _, S) -> {true, S};
instance(T, I, V, S) ->
  Key = utils:impl_key(T),
  case maps:find(Key, maps:get(I, S#solver.impls)) of
    {ok, {RawT, _, _, _}} ->
      {NormT, _} = norm_sig_type(RawT, true, S#solver.pid),
      IVs = utils:ivs(NormT),

      S1 = case IVs of
        [] -> S;
        _ ->
          #solver{
            inst_refs=InstRefs,
            iv_origins=IVOrigins,
            nested_ivs=NestedIVs
          } = S,

          Origins = maps:get({I, V}, IVOrigins),

          {NewInstRefs, NewNestedIVs} = ordsets:fold(fun({Ref, OrigV}, Memo) ->
            {FoldInstRefs, FoldNestedIVs} = Memo,
            {InstT, SubbedVs} = maps:get(Ref, FoldInstRefs),
            SubbedVs1 = add_subbed_vs(IVs, SubbedVs),

            FoldInstRefs1 = FoldInstRefs#{Ref => {InstT, SubbedVs1}},
            FoldNestedIVs1 = FoldNestedIVs#{{I, OrigV} => IVs},
            {FoldInstRefs1, FoldNestedIVs1}
          end, {InstRefs, NestedIVs}, Origins),

          NewIVOrigins = lists:foldl(fun({NestedIs, NestedV}, FoldIVOrigins) ->
            NestedOrigins = ordsets:fold(fun({Ref, _}, FoldOrigins) ->
              ordsets:add_element({Ref, NestedV}, FoldOrigins)
            end, ordsets:new(), Origins),

            ordsets:fold(fun(NestedI, NestedIVOrigins) ->
              NestedIVOrigins#{{NestedI, NestedV} => NestedOrigins}
            end, FoldIVOrigins, NestedIs)
          end, IVOrigins, IVs),

          S#solver{
            inst_refs=NewInstRefs,
            iv_origins=NewIVOrigins,
            nested_ivs=NewNestedIVs
          }
      end,

      % Unify T with NormT to ensure the instance is valid. But first, for
      % better error messages, replace V with NormT in FullT1 and FullT2. We
      % must do this in both FullT1 and FullT2 because we don't know which
      % contains V.
      #solver{t1=FullT1, t2=FullT2} = S1,
      Opts = #sub_opts{subs=#{V => NormT}},
      S2 = S1#solver{
        t1=utils:subs(FullT1, Opts),
        t2=utils:subs(FullT2, Opts)
      },
      {Valid, S3} = sub_unify(T, NormT, S2),
      {Valid, S3#solver{t1=FullT1, t2=FullT2}};

    error -> add_err(S)
  end.

add_subbed_vs(IVs, SubbedVs) ->
  lists:foldl(fun({Is, V}, FoldSubbedVs) ->
    % Rigid doesn't matter here, but note that these Vs are non-rigid
    % anyway because they're instantiated.
    FoldSubbedVs#{V => {tv, V, Is, false}}
  end, SubbedVs, IVs).

subs_s(T, S) -> subs_s(T, S, #sub_opts{}).

subs_s(T, #solver{subs=Subs, aliases=Aliases}, Opts) ->
  utils:subs(T, Opts#sub_opts{subs=Subs, aliases=Aliases}).

bound_vs(LEnv, #solver{schemes=Schemes}=S) ->
  maps:fold(fun
    (_, #binding{tv=TV, id=undefined}, FoldVs) ->
      ordsets:union(FoldVs, fvs(subs_s(TV, S)));

    (_, #binding{tv={tv, V, _, _}}, FoldVs) ->
      % 1) If a given other binding has been fully generalized already,
      %    we'll add the bound type variables from its scheme.
      % 2) If a given other binding is currently being generalized,
      %    its TV can be generalized over, and so we shouldn't add it here.
      case maps:find(V, Schemes) of
        {ok, {_, _, BoundVs}} -> ordsets:union(FoldVs, BoundVs);
        error -> FoldVs
      end
  end, ordsets:new(), LEnv).

fvs(T) ->
  FVsList = lists:filtermap(fun
    ({tv, V, _, _}) -> {true, V};
    ({gen, V, _, _, _}) ->
      % V only exists to track ifaces associated with this gen TV; it isn't a
      % regular type variable. That being said, it still must be included in FVs.
      % We assume FVs is a superset of IVs, and often use FVs to determine IVs;
      % V is an IV, and hence it must be incldued in FVs.
      {true, V};
    (_) -> false
  end, utils:tvs_list(T)),

  ordsets:from_list(FVsList).

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

gen_vs_list(T) ->
  lists:filtermap(fun
    ({gen, _, _, {tv, V, _, _}, _}=GenTV) -> {true, {V, GenTV}};
    (_) -> false
  end, utils:tvs_list(T)).

occurs(V, T) ->
  lists:any(fun
    ({tv, V1, _, _}) when V == V1 -> true;
    % occurs(true, T) means look for *any* rigid TV
    ({tv, _, _, Rigid}) when V == Rigid -> true;
    ({gen, V1, _, _, _}) when V == V1 -> true;
    (_) -> false
  end, utils:tvs_list(T)).
