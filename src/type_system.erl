-module(type_system).
-export([
  infer_file/1,
  infer_prg/1,
  report_errors/1,
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
%   errs - an array of error messages, each of the form {Msg, Line}
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
%   loc - the location of the current constraint that's being unified
%   from - a string describing where the current constraint is from
%   pid - the process id of the TV server used to generated fresh TVs
-record(solver, {
  subs = #{},
  errs = [],
  schemes = #{},
  bound_vs,
  structs = #{},
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

load() -> 'Lexer':'_@init'(gb_sets:new()).

infer_file(Path) ->
  {_, Comps, _} = parse_file(Path, #{}),
  case infer_comps(Comps) of
    {ok, Env} -> {ok, Env, Comps};
    {errors, _}=Errors -> Errors
  end.

parse_file(RawPath, Parsed) ->
  Path = case filename:extension(RawPath) of
    "" -> utils:absolute(RawPath ++ ".par");
    _ -> utils:absolute(RawPath)
  end,

  case maps:find(Path, Parsed) of
    {ok, Module} -> {Module, [], Parsed};
    error ->
      {ok, Binary} = file:read_file(Path),
      {ok, Tokens} = 'Lexer':tokenize(binary_to_list(Binary)),
      NormTokens = lists:map(fun(T) ->
        setelement(2, T, maps:get(start_line, element(2, T)))
      end, Tokens),

      {ok, Ast} = parser:parse(NormTokens),
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

      {Module, lists:append([[{Module, Ast, Deps, Path}] | Comps]), Parsed2}
  end.

infer_prg(Prg) ->
  {ok, Tokens} = if
    is_list(Prg) -> 'Lexer':tokenize(Prg);
    is_binary(Prg) -> 'Lexer':tokenize(Prg)
  end,
  NormTokens = lists:map(fun(T) ->
    setelement(2, T, maps:get(start_line, element(2, T)))
  end, Tokens),

  {ok, Ast} = parser:parse(NormTokens),
  % infer_prg should only be used only when there are no imports
  {module, _, {con_token, _, Module}, [], _} = Ast,
  %% ?LOG("Ast", Ast),

  Comps = [{Module, Ast, [], ""}],
  case infer_comps(Comps) of
    {ok, Env} -> {ok, Env, Comps};
    {errors, _}=Errors -> Errors
  end.

infer_comps(Comps) ->
  {ok, Pid} = tv_server:start_link(),

  {_, C} = lists:foldl(fun(Comp, {Modules, FoldC}) ->
    {Module, {module, Line, _, _, _}, _, _} = Comp,
    FoldC1 = FoldC#ctx{module=Module},
    case gb_sets:is_member(Module, Modules) of
      true -> {Modules, add_ctx_err(?ERR_REDEF_MODULE(Module), Line, FoldC1)};
      false -> {gb_sets:add(Module, Modules), FoldC1}
    end
  end, {gb_sets:new(), #ctx{pid=Pid}}, Comps),

  C1 = lists:foldl(fun({Module, {module, _, _, _, Defs}, _, _}, FoldC) ->
    lists:foldl(fun(Node, ModuleC) ->
      case Node of
        {global, Line, {var, _, Name}, _, Exported} ->
          case env_exists(Name, ModuleC) of
            true -> add_ctx_err(?ERR_REDEF(Name), Line, ModuleC);
            false ->
              {TV, ID} = tv_server:fresh_gnr_id(ModuleC#ctx.pid),
              env_add(Name, {add_dep, TV, ID}, Exported, ModuleC)
          end;

        {N, _, TE, _} when N == enum_token; N == struct_token ->
          {Line, RawCon, NumParams} = case TE of
            {con_token, Line_, RawCon_} -> {Line_, RawCon_, 0};
            {gen_te, _, {con_token, Line_, RawCon_}, ParamTEs} ->
              {Line_, RawCon_, length(ParamTEs)}
          end,

          Con = qualify(RawCon, ModuleC),
          Types = ModuleC#ctx.types,

          RedefBuiltin = (string:chr(RawCon, $.) == 0) and
            maps:is_key(RawCon, Types),
          Redef = maps:is_key(Con, Types),

          if
            RedefBuiltin ->
              add_ctx_err(?ERR_REDEF_BUILTIN_TYPE(RawCon), Line, ModuleC);

            % TODO: add line numbers for where redef occurred
            Redef -> add_ctx_err(?ERR_REDEF_TYPE(Con), Line, ModuleC);
            true -> ModuleC#ctx{types=Types#{Con => NumParams}}
          end;

        _ -> ModuleC
      end
    end, FoldC#ctx{module=Module}, Defs)
  end, C, Comps),

  C2 = lists:foldl(fun({Module, {module, _, _, _, Defs}, Deps, _}, FoldC) ->
    AccessibleModules = gb_sets:from_list([Module | Deps]),
    FoldC1 = FoldC#ctx{module=Module, modules=AccessibleModules},

    lists:foldl(fun(Node, ModuleC) ->
      case Node of
        {N, _, _, _} when N == enum_token; N == struct_token ->
          {_, ModuleC1} = infer(Node, ModuleC),
          ModuleC1;

        _ -> ModuleC
      end
    end, FoldC1, Defs)
  end, C1, Comps),

  C3 = lists:foldl(fun({Module, {module, _, _, _, Defs}, Deps, _}, FoldC) ->
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
        {global, Line, {var, _, Name}, Expr, _} ->
          {add_dep, TV, ID} = env_get(Name, ModuleC1),
          ModuleC2 = case Expr of
            {fn, _, _, _} -> ModuleC1;
            _ -> env_remove(Name, ModuleC1)
          end,

          ModuleC3 = new_gnr(TV, ID, ModuleC2),
          {T, ModuleC4} = infer(Expr, ModuleC3),
          ModuleC5 = add_cst(TV, T, Line, ?FROM_GLOBAL_DEF(Name), ModuleC4),

          ModuleC7 = if
            Sig == none -> ModuleC5;
            true ->
              {SigT, ModuleC6} = infer(Sig, ModuleC5),
              add_cst(TV, SigT, ?LOC(Sig), ?FROM_GLOBAL_SIG, ModuleC6)
          end,
          ModuleC8 = ModuleC7#ctx{env=ModuleC#ctx.env},
          {none, finish_gnr(ModuleC8, ModuleC#ctx.gnr)};

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
      {ok, SubbedEnv};

    {errors, Errs} -> {errors, Errs}
  end,

  % TODO: how to require that main is defined?
  ok = tv_server:stop(Pid),
  Result.

report_errors(Errs) ->
  lists:foreach(fun
    ({T1, T2, Line, From}) ->
      ?ERR(
        "[~p] in ~s~nexpected type ~s~ngot type      ~s~n~n",
        [Line, From, pretty(T1), pretty(T2)]
      );

    ({Msg, Line}) -> ?ERR("[~p] ~s~n", [Line, Msg])
  end, Errs).

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

infer({'::', Line, Expr, Sig}, C) ->
  G = C#ctx.gnr,
  {TV, ID} = tv_server:fresh_gnr_id(C#ctx.pid),

  {ExprT, C1} = infer(Expr, new_gnr(TV, ID, C)),
  {SigT, C2} = infer_sig(false, false, #{}, Sig, C1),
  NormSigT = norm_sig_type(SigT, maps:keys(C2#ctx.ifaces), C2#ctx.pid),

  C3 = add_cst(TV, ExprT, ?LOC(Expr), ?FROM_EXPR_SIG, C2),
  C4 = add_cst(TV, NormSigT, Line, ?FROM_EXPR_SIG, C3),
  C5 = finish_gnr(C4, add_gnr_dep(ID, G)),

  {{inst, TV}, C5};

infer({enum_token, _, EnumTE, Options}, C) ->
  {T, C1} = infer_sig(false, true, #{}, EnumTE, C),
  FVs = fvs(T),

  {_, C2} = lists:foldl(fun(Option, {Keys, FoldC}) ->
    {{con_token, Line, Con}, ArgTEs, KeyNode} = Option,
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
    FoldC3 = add_cst(TV, NormOptionT, Line, ?FROM_ENUM_CTOR, FoldC2),
    FoldC4 = finish_gnr(FoldC3, FoldC1#ctx.gnr),

    Name = utils:unqualify(Con),
    FoldC5 = case env_exists(Name, FoldC4) of
      true -> add_ctx_err(?ERR_REDEF(Name), Line, FoldC4);
      false -> env_add(Name, {add_dep, TV, ID}, true, FoldC4)
    end,

    case KeyNode of
      default ->
        Key = list_to_atom(Con),
        case maps:find(Key, Keys) of
          {ok, {default, _, _}} ->
            % we've already added an ERR_REDEF; no need to add another
            {Keys, FoldC5};
          {ok, {custom, _, CustomLine}} ->
            FoldC6 = add_ctx_err(
              ?ERR_DUP_KEY(Key, Con, Line),
              CustomLine,
              FoldC5
            ),
            {Keys, FoldC6};
          error -> {Keys#{Key => {default, Con, Line}}, FoldC5}
        end;

      {atom, KeyLine, Key} ->
        case maps:find(Key, Keys) of
          {ok, {_, OtherCon, OtherLine}} ->
            FoldC6 = add_ctx_err(
              ?ERR_DUP_KEY(Key, OtherCon, OtherLine),
              KeyLine,
              FoldC5
            ),

            % In case the map contains a default, we go ahead and replace the
            % value with a custom. This way, if another default comes up, we'll
            % correctly report an error.
            {Keys#{Key := {custom, Con, KeyLine}}, FoldC6};
          error -> {Keys#{Key => {custom, Con, KeyLine}}, FoldC5}
        end
    end
  end, {#{}, C1}, Options),

  {T, C2};

infer({struct_token, Line, StructTE, {record_te, _, Fields}=RecordTE}, C) ->
  {T, C1} = infer_sig(false, true, #{}, StructTE, C),
  {{record, _, RawFieldMap}, C2} = infer_sig(
    {T, fvs(T)},
    false,
    C1#ctx.ifaces,
    RecordTE,
    C1
  ),

  FnT = lists:foldr(fun({{var, _, Name}, _}, LastT) ->
    #{Name := FieldT} = RawFieldMap,
    {lam, FieldT, LastT}
  end, T, Fields),

  % don't need to make any Vs rigid; inst still works correctly
  NormFnT = norm_sig_type(FnT, [], C2#ctx.pid),

  {Con, ConLine, Value} = case {T, StructTE} of
    {{con, Con_}, {con_token, ConLine_, _}} ->
      {Con_, ConLine_, {T, [], RawFieldMap}};

    {{gen, Con_, ParamTs}, {gen_te, _, {con_token, ConLine_, _}, _}} ->
      Vs = lists:map(fun({tv, V, none, _}) -> V end, ParamTs),
      {Con_, ConLine_, {T, Vs, RawFieldMap}}
  end,

  {TV, ID} = tv_server:fresh_gnr_id(C2#ctx.pid),
  Name = utils:unqualify(Con),
  C3 = case env_exists(Name, C2) of
    true -> add_ctx_err(?ERR_REDEF(Name), ConLine, C2);
    false ->
      NewStructs = (C2#ctx.structs)#{Con => Value},
      env_add(Name, {add_dep, TV, ID}, true, C2#ctx{structs=NewStructs})
  end,

  C4 = new_gnr(TV, ID, C3),
  C5 = add_cst(TV, NormFnT, Line, ?FROM_STRUCT_CTOR, C4),
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

infer({cons, Line, Elems, Tail}, C) ->
  {T, C1} = infer({list, Line, Elems}, C),
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

infer({N, Line, Name}, C) when N == var; N == con_token; N == var_value ->
  lookup(C#ctx.module, Name, Line, C);

% only occurs when pattern matching to designate anything
infer({'_', _}, C) -> {tv_server:fresh(C#ctx.pid), C};

infer({record, _, Inits}, C) ->
  {FieldMap, C1} = lists:foldl(fun(Init, {Map, FoldC}) ->
    {{var, Line, Name}, Expr} = Init,
    {T, FoldC1} = infer(Expr, FoldC),

    case maps:is_key(Name, Map) of
      true -> {Map, add_ctx_err(?ERR_DUP_FIELD(Name), Line, FoldC1)};
      false -> {Map#{Name => T}, FoldC1}
    end
  end, {#{}, C}, Inits),

  {{record, tv_server:next_name(C#ctx.pid), FieldMap}, C1};

infer({update_record, Line, Expr, Inits}, C) ->
  {ExprT, C1} = infer(Expr, C),
  {{record, _, FieldMap}, C2} = infer({record, Line, Inits}, C1),

  RecordTV = tv_server:fresh(FieldMap, C2#ctx.pid),
  TV = tv_server:fresh(C2#ctx.pid),

  C3 = add_cst(TV, ExprT, Line, ?FROM_RECORD_UPDATE, C2),
  C4 = add_cst(TV, RecordTV, Line, ?FROM_RECORD_UPDATE, C3),
  {TV, C4};

infer({record, Line, {con_token, ConLine, Name}, Inits}, C) ->
  G = C#ctx.gnr,
  {TV, ID} = tv_server:fresh_gnr_id(C#ctx.pid),
  {RecordT, C1} = infer({record, Line, Inits}, new_gnr(TV, ID, C)),

  Con = qualify(Name, C1),
  case maps:find(Con, C1#ctx.structs) of
    {ok, {StructT, _, _}} ->
      NormSigT = norm_sig_type(StructT, [], C1#ctx.pid),
      From = ?FROM_RECORD_CREATE(Name),

      C2 = add_cst(TV, RecordT, Line, From, C1),
      C3 = add_cst(TV, NormSigT, Line, From, C2),
      C4 = finish_gnr(C3, add_gnr_dep(ID, G)),
      {{inst, TV}, C4};

    error -> {RecordT, add_ctx_err(?ERR_NOT_DEF_TYPE(Name), ConLine, C1)}
  end;

infer({field, _, {var, _, Name}}, C) ->
  FieldTV = tv_server:fresh(C#ctx.pid),
  TV = tv_server:fresh(#{Name => FieldTV}, C#ctx.pid),
  {{lam, TV, FieldTV}, C};

% TODO: ensure this is parsed correctly or add error cases (e.g. when var is
% a con_token, expr must be a con_token)
infer({field, Line, Expr, {N, VarLine, Name}=Var}, C)
    when N == var; N == con_token ->
  case Expr of
    {con_token, _, Module} ->
      case gb_sets:is_member(Module, C#ctx.modules) of
        % TODO: different error message for lookup in another module?
        true -> lookup(Module, Name, VarLine, C);
        false ->
          TV = tv_server:fresh(C#ctx.pid),
          {TV, add_ctx_err(?ERR_NOT_DEF_MODULE(Module), Line, C)}
      end;

    _ ->
      {ExprT, C1} = infer(Expr, C),
      {FieldT, C2} = infer({field, ?LOC(Var), Var}, C1),
      TV = tv_server:fresh(C2#ctx.pid),
      From = ?FROM_FIELD_ACCESS(element(3, Var)),
      C3 = add_cst({lam, ExprT, TV}, FieldT, Line, From, C2),
      {TV, C3}
  end;

infer({app, Line, Expr, Args}, C) ->
  {ExprT, C1} = infer(Expr, C),
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
  {TV, C3};

infer({native, Line, {atom, _, Module}, {var, _, Name}, Arity}, C) ->
  C1 = case erlang:function_exported(Module, list_to_atom(Name), Arity) of
    true -> C;
    false -> add_ctx_err(?ERR_NOT_DEF_NATIVE(Module, Name, Arity), Line, C)
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
      C5 = add_cst(TV, ThenT, ?LOC(Then), ?FROM_IF_BODY, C4),
      C6 = add_cst(TV, ElseT, ?LOC(Else), ?FROM_IF_BODY, C5),
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
      C5 = add_cst(TV, ThenT, ?LOC(Then), ?FROM_IF_LET_BODY, C4),
      C6 = add_cst(TV, ElseT, ?LOC(Else), ?FROM_IF_LET_BODY, C5),
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

infer({Op, Line, Left, Right}, C) ->
  {LeftT, C1} = infer(Left, C),
  {RightT, C2} = infer(Right, C1),

  TV = tv_server:fresh(C2#ctx.pid),

  {T1, T2} = if
    Op == '=='; Op == '!=' ->
      OperandTV = tv_server:fresh(C2#ctx.pid),
      {
        {lam, LeftT, {lam, RightT, TV}},
        {lam, OperandTV, {lam, OperandTV, {con, "Bool"}}}
      };
    Op == '||'; Op == '&&' -> {
      {lam, LeftT, {lam, RightT, TV}},
      {lam, {con, "Bool"}, {lam, {con, "Bool"}, {con, "Bool"}}}
    };
    Op == '|>' ->
      ArgTV = tv_server:fresh(C2#ctx.pid),
      {
        {lam, LeftT, {lam, RightT, TV}},
        {lam, ArgTV, {lam, {lam, ArgTV, TV}, TV}}
      };
    Op == '>'; Op == '<'; Op == '>='; Op == '<=' ->
      NumTV = tv_server:fresh("Num", C2#ctx.pid),
      {
        {lam, LeftT, {lam, RightT, TV}},
        {lam, NumTV, {lam, NumTV, {con, "Bool"}}}
      };
    Op == '+'; Op == '-'; Op == '*'; Op == '/' ->
      NumTV = tv_server:fresh("Num", C2#ctx.pid),
      ReturnT = if Op == '/' -> {con, "Float"}; true -> NumTV end,
      {
        {lam, LeftT, {lam, RightT, TV}},
        {lam, NumTV, {lam, NumTV, ReturnT}}
      };
    Op == '%' ->
      ReturnTV = tv_server:fresh("Num", C2#ctx.pid),
      {
        {lam, LeftT, {lam, RightT, TV}},
        {lam, {con, "Int"}, {lam, {con, "Int"}, ReturnTV}}
      };
    Op == '++' ->
      OperandTV = tv_server:fresh("Concatable", C2#ctx.pid),
      {
        {lam, LeftT, {lam, RightT, TV}},
        {lam, OperandTV, {lam, OperandTV, OperandTV}}
      };
    Op == '--' ->
      OperandTV = tv_server:fresh("Separable", C2#ctx.pid),
      {
        {lam, LeftT, {lam, RightT, TV}},
        {lam, OperandTV, {lam, OperandTV, OperandTV}}
      }
  end,

  C3 = add_cst(T1, T2, Line, ?FROM_OP(Op), C2),
  {TV, C3};

infer({Op, Line, Expr}, C) ->
  {ExprT, C1} = infer(Expr, C),
  TV = tv_server:fresh(C1#ctx.pid),

  {T1, T2} = if
    Op == '!' -> {{lam, ExprT, TV}, {lam, {con, "Bool"}, {con, "Bool"}}};
    Op == '#' ->
      ElemT = tv_server:fresh(C1#ctx.pid),
      {{lam, ExprT, TV}, {lam, {gen, "List", [ElemT]}, {gen, "Set", [ElemT]}}};
    Op == '$' -> {{lam, ExprT, TV}, {lam, {con, "Char"}, {con, "Int"}}};
    Op == '-' ->
      NumT = tv_server:fresh("Num", C1#ctx.pid),
      {{lam, ExprT, TV}, {lam, NumT, NumT}};
    Op == 'discard' -> {TV, none}
  end,

  C2 = add_cst(T1, T2, Line, ?FROM_OP(Op), C1),
  {TV, C2}.

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
infer_sig_helper(RestrictVs, Unique, {gen_te, Line, ConToken, ParamTEs}, C) ->
  {con_token, _, RawCon} = ConToken,
  Con = qualify(RawCon, C),

  {Valid, C1} = case Unique of
    false -> validate_type(Con, length(ParamTEs), Line, C);
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
infer_sig_helper(RestrictVs, Unique, {tv_te, Line, V, TE}, C) ->
  C1 = case RestrictVs of
    false -> C;
    {T, AllowedVs} ->
      case gb_sets:is_member(V, AllowedVs) of
        true -> C;
        false ->
          case T of
            % T is already an invalid type; no need to add another error
            {tv, _, _, _} -> C;
            _ -> add_ctx_err(?ERR_TV_SCOPE(V, element(2, T)), Line, C)
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
        {true, _} -> add_ctx_err(?ERR_REDEF_TV(V), ?LOC(TE), C2);
        {false, I} -> C2;
        {false, _} ->
          add_ctx_err(?ERR_TV_IFACE(V, ExpI, I), ?LOC(TE), C2)
      end;
    error -> C2#ctx{ifaces=Ifaces#{V => I}}
  end,

  % This TV should be rigid in signatures, but it'll be reset to flex in
  % norm_sig_type. Hence, we don't set rigid here, but rather after renaming.
  {{tv, V, I, false}, C3};
infer_sig_helper(_, Unique, {con_token, Line, RawCon}, C) ->
  Con = qualify(RawCon, C),
  {Valid, C1} = case Unique of
    false -> validate_type(Con, 0, Line, C);
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
    {var, Line, Name} = Var,
    {FieldT, FoldC1} = infer_sig_helper(RestrictVs, Unique, FieldTE, FoldC),

    case maps:is_key(Name, FoldMap) of
      true -> {FoldMap, add_ctx_err(?ERR_DUP_FIELD(Name), Line, FoldC1)};
      false -> {FoldMap#{Name => FieldT}, FoldC1}
    end
  end, {#{}, C}, Fields),

  {{record, tv_server:next_name(C1#ctx.pid), FieldMap}, C1};
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

infer_pattern({var, Line, Name}=Pattern, {fn, _, _, _}=Expr, From, C) ->
  {TV, ID} = tv_server:fresh_gnr_id(C#ctx.pid),
  C1 = env_add(Name, {add_dep, TV, ID}, false, C),
  {PatternT, C2} = infer(Pattern, new_gnr(TV, ID, C1)),
  {ExprT, C3} = infer(Expr, C2),
  C4 = add_cst(PatternT, ExprT, Line, From, C3),
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

lookup(Module, Name, Line, C) ->
  Key = {Module, Name},
  External = C#ctx.module /= Module,

  case maps:find(Key, C#ctx.env) of
    {ok, {_, false}} when External ->
      TV = tv_server:fresh(C#ctx.pid),
      {TV, add_ctx_err(?ERR_NOT_EXPORTED(Name, Module), Line, C)};

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
        External -> add_ctx_err(?ERR_NOT_DEF(Name, Module), Line, C);
        true -> add_ctx_err(?ERR_NOT_DEF(Name), Line, C)
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

add_cst(T1, T2, Line, From, C) ->
  G = C#ctx.gnr,
  Loc = {C#ctx.module, Line},
  G1 = G#gnr{csts=[{T1, T2, Loc, From} | G#gnr.csts]},
  C#ctx{gnr=G1}.

validate_type(Con, NumParams, Line, C) ->
  case maps:find(Con, C#ctx.types) of
    {ok, NumParams} -> {true, C};
    {ok, ExpNumParams} ->
      Msg = ?ERR_TYPE_PARAMS(Con, ExpNumParams, NumParams),
      {false, add_ctx_err(Msg, Line, C)};
    % TODO: better messages when module is not defined (e.g. Bad.Type) and
    % module is defined but no such type exists (e.g. Module.Bad)
    error -> {false, add_ctx_err(?ERR_NOT_DEF_TYPE(Con), Line, C)}
  end.

add_ctx_err(Msg, Line, C) ->
  Loc = {C#ctx.module, Line},
  C#ctx{errs=[{Msg, Loc} | C#ctx.errs]}.

norm_sig_type(SigT, RigidVs, Pid) ->
  RigidVsSet = gb_sets:from_list(RigidVs),

  % TODO: is it more intuitive to change each fv to *fv and then replace?
  Subs = gb_sets:fold(fun(V, FoldSubs) ->
    case gb_sets:is_member(V, RigidVsSet) of
      true -> FoldSubs#{V => {rigid, tv_server:next_name(Pid)}};
      false -> FoldSubs#{V => tv_server:next_name(Pid)}
    end
  end, #{}, fvs(SigT)),

  subs(SigT, Subs).

solve(Gs, S) ->
  Map = lists:foldl(fun(G, FoldMap) -> FoldMap#{G#gnr.id => G} end, #{}, Gs),
  %% ?LOG("Gs", lists:map(fun(G) -> G#gnr{csts=pretty_csts(G#gnr.csts)} end, Gs)),

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

      %% ?LOG("Subs", maps:map(fun(_, T) -> pretty(T) end, S3#solver.subs)),

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
  lists:foldl(fun({T1, T2, Loc, From}, FoldS) ->
    FoldS1 = FoldS#solver{loc=Loc, from=From},
    unify(resolve(T1, FoldS), resolve(T2, FoldS), FoldS1)
  end, S#solver{bound_vs=BoundVs}, OrderedCsts).

resolve({lam, ArgT, ReturnT}, S) ->
  {lam, resolve(ArgT, S), resolve(ReturnT, S)};
resolve({tuple, ElemTs}, S) ->
  {tuple, lists:map(fun(T) -> resolve(T, S) end, ElemTs)};
resolve({tv, V, I, Rigid}, S) ->
  if
    is_map(I) ->
      NewI = maps:map(fun(_, T) -> resolve(T, S) end, I),
      {tv, V, NewI, Rigid};
    true -> {tv, V, I, Rigid}
  end;
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

unify({tuple, ElemTs1}, {tuple, ElemTs2}, S) ->
  if
    length(ElemTs1) /= length(ElemTs2) ->
      add_err({tuple, ElemTs1}, {tuple, ElemTs2}, S);

    true ->
      lists:foldl(fun({T1, T2}, FoldS) ->
        unify(T1, T2, FoldS)
      end, S, lists:zip(ElemTs1, ElemTs2))
  end;

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

unify({gen, Con, ParamTs1}, {gen, Con, ParamTs2}, S) ->
  if
    length(ParamTs1) /= length(ParamTs2) ->
      add_err({gen, Con, ParamTs1}, {gen, Con, ParamTs2}, S);

    true ->
      lists:foldl(fun({T1, T2}, FoldS) ->
        unify(T1, T2, FoldS)
      end, S, lists:zip(ParamTs1, ParamTs2))
  end;

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
  #solver{subs=Subs, loc=Loc, from=From} = S,
  Err = {subs(T1, Subs), subs(T2, Subs), Loc, From},
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
  case maps:find(Con, S#solver.structs) of
    {ok, {_, [], RawFieldMap}} -> {record, none, RawFieldMap};
    error -> {con, Con}
  end;
unalias({gen, Con, ParamTs}, S) ->
  case maps:find(Con, S#solver.structs) of
    {ok, {_, Vs, RawFieldMap}} ->
      Subs = maps:from_list(lists:zip(Vs, ParamTs)),
      subs({record, none, RawFieldMap}, Subs);
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

subs({lam, ArgT, ReturnT}, Subs) ->
  {lam, subs(ArgT, Subs), subs(ReturnT, Subs)};
subs({tuple, ElemTs}, Subs) ->
  {tuple, lists:map(fun(T) -> subs(T, Subs) end, ElemTs)};
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
subs({gen, Con, ParamTs}, Subs) ->
  {gen, Con, lists:map(fun(T) -> subs(T, Subs) end, ParamTs)};
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
  maps:fold(fun(_, {Value, _}, FoldVs) ->
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
fvs({tuple, ElemTs}) ->
  lists:foldl(fun(T, FVs) ->
    gb_sets:union(FVs, fvs(T))
  end, gb_sets:new(), ElemTs);
fvs({tv, V, I, _}) ->
  if
    is_map(I) -> gb_sets:add(V, fvs({record, none, I}));
    true -> gb_sets:singleton(V)
  end;
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
fvs(none) -> gb_sets:new().

occurs(V, {lam, ArgT, ReturnT}) ->
  occurs(V, ArgT) or occurs(V, ReturnT);
occurs(V, {tuple, ElemTs}) ->
  lists:foldl(fun(T, Occurs) ->
    Occurs or occurs(V, T)
  end, false, ElemTs);
occurs(V, {tv, V1, I, Rigid}) ->
  OccursI = if
    is_map(I) -> occurs(V, {record, none, I});
    true -> false
  end,
  OccursI or (V == Rigid) or (V == V1);
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
occurs(_, none) -> false.

%% pretty_csts([]) -> [];
%% pretty_csts([{T1, T2, Line, From} | Rest]) ->
%%   [{pretty(T1), pretty(T2), Line, From} | pretty_csts(Rest)].

pretty({lam, ArgT, ReturnT}) ->
  Format = case ArgT of
    {lam, _, _} -> "(~s) -> ~s";
    _ -> "~s -> ~s"
  end,
  ?FMT(Format, [pretty(ArgT), pretty(ReturnT)]);
pretty({tuple, ElemTs}) ->
  PrettyElemTs = lists:map(fun(T) -> pretty(T) end, ElemTs),
  ?FMT("(~s)", [string:join(PrettyElemTs, ", ")]);
pretty({tv, V, I, Rigid}) ->
  Str = if
    I == none -> tl(V);
    is_map(I) -> ?FMT("{ ~s | ~s }", [tl(V), pretty_field_map(I)]);
    true -> ?FMT("~s: ~s", [tl(V), I])
  end,

  case Rigid of
    false -> Str;
    true -> ?FMT("rigid(~s)", [Str])
  end;
pretty({set_iface, I}) ->
  Str = if
    is_map(I) -> pretty_field_map(I);
    true -> I
  end,
  ?FMT("I = ~s", [Str]);
% TODO: keep qualified when ambiguous
pretty({con, Con}) -> utils:unqualify(Con);
pretty({gen, "List", [ElemT]}) ->
  ?FMT("[~s]", [pretty(ElemT)]);
pretty({gen, Con, ParamTs}) ->
  PrettyParamTs = lists:map(fun(T) -> pretty(T) end, ParamTs),
  ?FMT("~s<~s>", [utils:unqualify(Con), string:join(PrettyParamTs, ", ")]);
pretty({inst, TV}) ->
  ?FMT("inst(~s)", [pretty(TV)]);
pretty({record, _, FieldMap}) ->
  ?FMT("{ ~s }", [pretty_field_map(FieldMap)]);
pretty(none) -> "()".

pretty_field_map(FieldMap) ->
  FieldStrs = maps:fold(fun(Name, T, Strs) ->
    [?FMT("~s :: ~s", [Name, pretty(T)]) | Strs]
  end, [], FieldMap),
  string:join(lists:sort(FieldStrs), ", ").
