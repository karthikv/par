-module(code_gen).
-export([compile_comps/2, counter_run/1, excluder_run/1]).

-include("common.hrl").
-define(COUNTER_NAME, code_gen_counter).
-define(EXCLUDER_NAME, code_gen_excluder).
-define(INIT_FN_ATOM, '_@init').

-record(cg, {env, in_pattern = false, ctx}).

compile_comps(Comps, C) ->
  CG = #cg{env=#{}, ctx=C},
  {AllExports, CG1} = lists:mapfoldl(fun(Comp, FoldCG) ->
    {Exports, FoldCG1} = populate_env(Comp, FoldCG),
    {lists:append(Exports), FoldCG1}
  end, CG, Comps),

  CG2 = lists:foldl(fun populate_direct_imports/2, CG1, Comps),

  lists:map(fun({Comp, Exports}) ->
    compile_ast(Comp, Exports, CG2)
  end, lists:zip(Comps, AllExports)).

populate_env(#comp{module=Module, ast=Ast}, CG) ->
  {module, _, _, _, Defs} = Ast,

  % populate env and aggregate exports
  lists:mapfoldl(fun(Node, ModuleCG) ->
    case Node of
      {global, _, {var, _, Name}, {fn, _, Args, _}, Exported} ->
        Atom = list_to_atom(Name),
        Arity = length(Args),
        Value = {{global_fn, Atom}, Arity},

        ModuleCG1 = env_set(Name, Value, ModuleCG),
        if
          Exported or ((Name == "main") and (Arity == 0)) ->
            {[{Atom, Arity}], ModuleCG1};
          true -> {[], ModuleCG1}
        end;

      {global, _, {var, _, Name}, _, Exported} ->
        Atom = list_to_atom(Name),
        Value = {{global, Atom}, unknown},

        ModuleCG1 = env_set(Name, Value, ModuleCG),
        case Exported of
          true -> {[{Atom, 0}], ModuleCG1};
          false -> {[], ModuleCG1}
        end;

      {enum, _, EnumTE, OptionTEs} ->
        EnumCon = case EnumTE of
          {con_token, _, EnumCon_} -> EnumCon_;
          {gen_te, _, {con_token, _, EnumCon_}, _} -> EnumCon_
        end,
        IDAtom = id_atom(EnumCon, ModuleCG),

        {Exports, ModuleCG1} = lists:mapfoldl(fun(OptionTE, FoldCG) ->
          {option, _, {con_token, _, Con}, ArgsTE, KeyNode} = OptionTE,

          Atom = list_to_atom(Con),
          Arity = length(ArgsTE),
          Key = case KeyNode of
            none -> Atom;
            {some, {atom, _, Key_}} -> Key_
          end,

          case Arity of
            0 ->
              Value = {{option, IDAtom, Key}, badarity},
              {[], env_set(Con, Value, FoldCG)};
            _ ->
              Value = {{option, IDAtom, Key, Atom}, Arity},
              {[{Atom, Arity}], env_set(Con, Value, FoldCG)}
          end
        end, ModuleCG, OptionTEs),

        {lists:append(Exports), ModuleCG1};

      {struct, _, {con_token, _, Con}, FieldTEs} ->
        Atom = list_to_atom(Con),
        Arity = length(FieldTEs),
        Value = {{global_fn, Atom}, Arity},
        {[{Atom, Arity}], env_set(Con, Value, ModuleCG)};

      {struct, _, {gen_te, _, {con_token, _, Con}, _}, FieldTEs} ->
        Atom = list_to_atom(Con),
        Arity = length(FieldTEs),
        Value = {{global_fn, Atom}, Arity},
        {[{Atom, Arity}], env_set(Con, Value, ModuleCG)};

      {interface, _, {con_token, _, RawCon}, Fields} ->
        #cg{ctx=#ctx{ifaces=Ifaces, impls=Impls}=C} = ModuleCG,
        Con = utils:qualify(RawCon, C),
        {_, FieldMetas} = maps:get(Con, Ifaces),
        SubImpls = maps:get(Con, Impls),

        {Exports, ModuleCG1} = lists:mapfoldl(fun({Sig, FieldMeta}, FoldCG) ->
          {sig, _, {var, _, Name}, _} = Sig,
          Atom = list_to_atom(Name),
          {_, Arity} = FieldMeta,

          Value = {{global_fn, Atom}, Arity},
          {{Atom, Arity}, env_set(Name, Value, FoldCG)}
        end, ModuleCG, lists:zip(Fields, FieldMetas)),

        ModuleCG2 = lists:foldl(fun({Key, {_, Inits}}, FoldCG) ->
          lists:foldl(fun({init, _, {var, _, Name}, Expr}, NestedCG) ->
            FieldName = impl_field_name(Con, Key, Name),
            FieldAtom = list_to_atom(FieldName),

            Value = case Expr of
              {fn, _, Args, _} -> {{global_fn, FieldAtom}, length(Args)};
              _ -> {{global, FieldAtom}, unknown}
            end,
            env_set(FieldName, Value, NestedCG)
          end, FoldCG, Inits)
        end, ModuleCG1, maps:to_list(SubImpls)),

        {Exports, ModuleCG2};

      _ -> {[], ModuleCG}
    end
  end, set_module(Module, CG), Defs).

impl_clauses(Con, Name, Args, ArgsRep, TargetRep, Loc, CG) ->
  Line = ?START_LINE(Loc),
  ImplMap = maps:get(Con, CG#cg.ctx#ctx.impls),
  Keys = maps:keys(ImplMap),
  Enums = CG#cg.ctx#ctx.enums,
  Structs = CG#cg.ctx#ctx.structs,

  Conds = lists:filtermap(fun(Key) ->
    ElementRep = call(erlang, element, [eabs(1, Line), TargetRep], Line),

    When = case Key of
      "()" -> {op, Line, '==', TargetRep, {tuple, Line, []}};
      "Record" -> {op, Line, '==', ElementRep, eabs('%Record', Line)};
      "Set" -> {op, Line, '==', ElementRep, eabs('%Set', Line)};
      _ ->
        case maps:is_key(Key, Enums) orelse maps:is_key(Key, Structs) of
          true ->
            IDRep = eabs(id_atom(Key, CG), Line),
            {op, Line, '==', ElementRep, IDRep};
          false -> false
        end
    end,

    case When of
      false -> false;
      _ ->
        Body = impl_field_body(Con, Key, Name, Args, Loc, CG),
        {true, {clause, Line, [], [[When]], Body}}
    end
  end, Keys),

  TupleConds = case maps:is_key("Tuple", ImplMap) of
    true ->
      TupleBody = impl_field_body(Con, "Tuple", Name, Args, Loc, CG),
      Conds ++ [{clause, Line, [], [[{atom, Line, true}]], TupleBody}];
    false -> Conds
  end,

  IsTuple = call(erlang, is_tuple, [TargetRep], Line),
  TupleIf = {'if', Line, TupleConds},
  TupleClause = {clause, Line, ArgsRep, [[IsTuple]], [TupleIf]},

  OtherClauses = lists:filtermap(fun(Key) ->
    FnAtom = case Key of
      "Int" -> is_integer;
      "Float" -> is_float;
      "Bool" -> is_boolean;
      "Atom" -> is_atom;
      "String" -> is_binary;
      "Ref" -> is_reference;
      "List" -> is_list;
      "Map" -> is_map;
      "Function" -> is_function;
      _ -> false
    end,

    case FnAtom of
      false -> false;
      _ ->
        When = call(erlang, FnAtom, [TargetRep], Line),
        Body = impl_field_body(Con, Key, Name, Args, Loc, CG),
        {true, {clause, Line, ArgsRep, [[When]], Body}}
    end
  end, Keys),

  [TupleClause | OtherClauses].

id_atom(RawCon, CG) ->
  Con = utils:resolve_con(RawCon, CG#cg.ctx),
  list_to_atom([$% | Con]).

impl_field_body(Con, Key, Name, Args, Loc, CG) ->
  FieldName = impl_field_name(Con, Key, Name),
  [rep({app, Loc, {var, Loc, FieldName}, Args}, CG)].

impl_field_name(Con, Key, Name) ->
  lists:concat(["_@impl@", Con, [$@ | Key], [$@ | Name]]).

populate_direct_imports(#comp{module=Module, deps=Deps}, CG) ->
  Enums = CG#cg.ctx#ctx.enums,
  lists:foldl(fun({DepModule, Idents}, ModuleCG) ->
    lists:foldl(fun(Ident, NestedCG) ->
      case Ident of
        {var, _, Name} ->
          {_, Arity} = maps:get({DepModule, Name}, NestedCG#cg.env),
          env_set(Name, {{external, DepModule}, Arity}, NestedCG);

        {con_token, _, Name} ->
          % Name may refer to a type or a variant. We don't need to import
          % types, so only import the variant if it exists.
          case maps:find({DepModule, Name}, NestedCG#cg.env) of
            {ok, {_, Arity}} ->
              env_set(Name, {{external, DepModule}, Arity}, NestedCG);
            error -> NestedCG
          end;

        {variants, _, Name} ->
          Con = lists:concat([DepModule, '.', Name]),
          Variants = maps:get(Con, Enums),

          lists:foldl(fun(Variant, FoldCG) ->
            {_, Arity} = maps:get({DepModule, Variant}, FoldCG#cg.env),
            env_set(Variant, {{external, DepModule}, Arity}, FoldCG)
          end, NestedCG, Variants)
      end
    end, ModuleCG, Idents)
  end, set_module(Module, CG), Deps).

compile_ast(Comp, Exports, CG) ->
  #comp{module=Module, ast=Ast, path=Path} = Comp,
  counter_spawn(),
  excluder_spawn(gb_sets:from_list([
    '_@curry',
    '_@concat',
    '_@separate',
    '_@gm_find',
    '_@gm_set'
  ])),

  {module, _, _, _, Defs} = Ast,
  ModuleCG = set_module(Module, CG),
  Reps = lists:flatten(lists:map(fun(Node) -> rep(Node, ModuleCG) end, Defs)),

  % remove everything except necessary functions
  Excluded = excluder_all(),
  Utils = lists:filter(fun
    ({function, _, Atom, _, _}) -> not gb_sets:is_member(Atom, Excluded);
    (_) -> false
  end, code_gen_utils_parsed:forms()),

  {function, _, InitAtom, InitArity, _}=InitRep = rep_init_fn(Comp),

  LibForms = [
    {attribute, 1, file, {"[par-compiler]", 1}},
    {attribute, 1, module, list_to_atom(Module)},
    {attribute, 1, compile, [no_auto_import]},
    {attribute, 1, export, [{InitAtom, InitArity} | Exports]},
    InitRep |
    Utils
  ],
  CodeForms = [{attribute, 1, file, {Path, 1}} | Reps],

  {ok, Mod, Binary} = compile:forms(LibForms ++ CodeForms, debug_info),
  {Mod, Binary}.

rep({global, Loc, {var, _, Name}, Expr, _}, CG) ->
  Line = ?START_LINE(Loc),

  case Expr of
    {fn, _, Args, _} ->
      {'fun', _, {clauses, Clauses}} = rep(Expr, CG),
      {function, Line, list_to_atom(Name), length(Args), Clauses};

    _ ->
      {{global, Atom}, _} = env_get(Name, CG),
      Gm = gm(CG#cg.ctx#ctx.module),

      excluder_remove('_@gm_find'),
      excluder_remove('_@gm_set'),

      FindCall = {call, Line, {atom, Line, '_@gm_find'},
        [{atom, Line, Gm}, {atom, Line, Atom}]},
      SetCall = {call, Line, {atom, Line, '_@gm_set'},
        [{atom, Line, Gm}, {atom, Line, Atom}, rep(Expr, CG)]},

      Var = {var, Line, unique("_@Value")},
      Case = {'case', Line, FindCall, [
        {clause, Line, [{tuple, Line, [{atom, Line, ok}, Var]}], [], [Var]},
        {clause, Line, [{atom, Line, error}], [], [SetCall]}
      ]},

      Clause = {clause, Line, [], [], [Case]},
      {function, Line, list_to_atom(Name), 0, [Clause]}
  end;

rep({enum, _, EnumTE, OptionTEs}, CG) ->
  FnOptionTEs = lists:filter(fun({option, _, _, ArgsTE, _}) ->
    length(ArgsTE) > 0
  end, OptionTEs),

  EnumCon = case EnumTE of
    {con_token, _, EnumCon_} -> EnumCon_;
    {gen_te, _, {con_token, _, EnumCon_}, _} -> EnumCon_
  end,
  IDAtom = id_atom(EnumCon, CG),

  lists:map(fun({option, _, {con_token, ConLoc, Con}, ArgsTE, KeyNode}) ->
    Line = ?START_LINE(ConLoc),
    ArgsRep = lists:map(fun(_) ->
      Atom = unique("_@Arg"),
      {var, Line, Atom}
    end, ArgsTE),

    ConAtom = list_to_atom(Con),
    {KeyLine, Key} = case KeyNode of
      none -> {Line, ConAtom};
      {some, {atom, KeyLoc, Key_}} -> {?START_LINE(KeyLoc), Key_}
    end,

    IDRep = eabs(IDAtom, Line),
    Body = [{tuple, Line, [IDRep, {atom, KeyLine, Key} | ArgsRep]}],
    Clause = {clause, Line, ArgsRep, [], Body},
    {function, Line, ConAtom, length(ArgsTE), [Clause]}
  end, FnOptionTEs);

rep({struct, Loc, StructTE, FieldTEs}, CG) ->
  {Line, Con} = case StructTE of
    {con_token, ConLoc, Con_} -> {?START_LINE(ConLoc), Con_};
    {gen_te, _, {con_token, ConLoc, Con_}, _} -> {?START_LINE(ConLoc), Con_}
  end,

  {ArgsRep, CG1} = lists:mapfoldl(fun(Sig, FoldCG) ->
    {sig, _, {var, _, FieldName}=Var, _} = Sig,
    FoldCG1 = bind(FieldName, unknown, FoldCG),
    {rep(Var, FoldCG1), FoldCG1}
  end, CG, FieldTEs),

  Pairs = lists:map(fun({sig, _, {var, FieldLoc, FieldName}=Var, _}) ->
    {{atom, FieldLoc, list_to_atom(FieldName)}, Var}
  end, FieldTEs),
  IDRep = eabs(id_atom(Con, CG), Line),
  Body = [{tuple, Line, [IDRep, rep({map, Loc, Pairs}, CG1)]}],

  Clause = {clause, Line, ArgsRep, [], Body},
  {function, Line, list_to_atom(Con), length(FieldTEs), [Clause]};

rep({interface, _, {con_token, _, RawCon}, Fields}, CG) ->
  #cg{ctx=#ctx{ifaces=Ifaces, impls=Impls}=C} = CG,
  Con = utils:qualify(RawCon, C),
  {_, FieldMetas} = maps:get(Con, Ifaces),
  SubImpls = maps:get(Con, Impls),

  IfaceReps = lists:map(fun({{sig, Loc, {var, _, Name}, _}, {ArgNum, Arity}}) ->
    Line = ?START_LINE(Loc),
    {Args, CG1} = lists:mapfoldl(fun(Num, FoldCG) ->
      ArgName = lists:concat(["_@Arg", Num]),
      FoldCG1 = bind(ArgName, unknown, FoldCG),
      {{var, Loc, ArgName}, FoldCG1}
    end, CG, lists:seq(1, Arity)),

    ArgsRep = lists:map(fun(Arg) -> rep(Arg, CG1) end, Args),
    TargetRep = lists:nth(ArgNum, ArgsRep),

    Clauses = impl_clauses(Con, Name, Args, ArgsRep, TargetRep, Loc, CG1),
    {function, Line, list_to_atom(Name), Arity, Clauses}
  end, lists:zip(Fields, FieldMetas)),

  ImplReps = lists:flatmap(fun({Key, {_, Inits}}) ->
    lists:map(fun({init, Loc, {var, VarLoc, Name}, Expr}) ->
      FieldName = impl_field_name(Con, Key, Name),
      rep({global, Loc, {var, VarLoc, FieldName}, Expr, false}, CG)
    end, Inits)
  end, maps:to_list(SubImpls)),

  [IfaceReps, ImplReps];

rep({impl, _, _, _, _}, _) -> [];
rep({sig, _, _, _}, _) -> [];

rep({fn, Loc, Args, Expr}, CG) ->
  Names = gb_sets:union(lists:map(fun type_system:pattern_names/1, Args)),
  CG1 = gb_sets:fold(fun(Name, FoldCG) ->
    bind(Name, unknown, FoldCG)
  end, CG, Names),

  Patterns = lists:map(fun(Pattern) ->
    rep(Pattern, CG1#cg{in_pattern=true})
  end, Args),

  Line = ?START_LINE(Loc),
  Clause = {clause, Line, Patterns, [], [rep(Expr, CG1)]},
  {'fun', Line, {clauses, [Clause]}};

rep({binary_op, _, ':', Expr, _}, CG) -> rep(Expr, CG);

rep({unit, Loc}, _) -> eabs({}, ?START_LINE(Loc));
rep({N, Loc, V}, _)
  when N == int; N == float; N == bool; N == str; N == atom ->
    eabs(V, ?START_LINE(Loc));
rep({char, Loc, V}, _) ->
  % special case; erl_parse:abstract will give us {integer, _, _}
  {char, ?START_LINE(Loc), V};

% only occurs in patterns
rep({'_', Loc}, _) -> {var, ?START_LINE(Loc), '_'};

rep({list, Loc, Elems}, CG) ->
  lists:foldr(fun(E, FoldRep) ->
    ERep = rep(E, CG),
    {cons, element(2, ERep), ERep, FoldRep}
  end, {nil, ?START_LINE(Loc)}, Elems);

rep({cons, _, Elems, Tail}, CG) ->
  lists:foldr(fun(E, FoldRep) ->
    ERep = rep(E, CG),
    {cons, element(2, ERep), ERep, FoldRep}
  end, rep(Tail, CG), Elems);

rep({tuple, Loc, Elems}, CG) ->
  {tuple, ?START_LINE(Loc), lists:map(fun(E) -> rep(E, CG) end, Elems)};

rep({map, Loc, Pairs}, CG) ->
  PairsRep = lists:map(fun({K, V}) ->
    KRep = rep(K, CG),
    VRep = rep(V, CG),
    {map_field_assoc, element(2, KRep), KRep, VRep}
  end, Pairs),
  {map, ?START_LINE(Loc), PairsRep};

rep({N, Loc, Name}, CG) when N == var; N == con_token; N == var_value ->
  Line = ?START_LINE(Loc),
  case env_get(Name, CG) of
    % global variable handled by the global manager
    {{global, Atom}, _} -> {call, Line, {atom, Line, Atom}, []};
    {{option, IDAtom, Key}, _} ->
      {tuple, Line, [eabs(IDAtom, Line), {atom, Line, Key}]};
    {{option, _, _, Atom}, Arity} -> {'fun', Line, {function, Atom, Arity}};
    {{global_fn, Atom}, Arity} -> {'fun', Line, {function, Atom, Arity}};
    {{external, Module}, _} ->
      rep({field, Loc, {con_token, Loc, Module}, {N, Loc, Name}}, CG);
    {Atom, _} when is_atom(Atom) -> {var, Line, Atom}
  end;

rep({anon_record, Loc, Ref, Inits}, CG) ->
  PairsRep = lists:map(fun({init, _, {var, VarLoc, Name}, Expr}) ->
    Line = ?START_LINE(VarLoc),

    ExprRep = case Expr of
      {fn, _, Args, _} ->
        % We're unsure whether the named fun is going to be used (i.e. whether
        % the named fun is recursive), so we give it a name prefixed with an
        % underscore to prevent unused errors.
        Atom = unique([$_ | Name]),
        CG1 = env_set(Name, {Atom, length(Args)}, CG),

        {'fun', FunLine, {clauses, Clauses}} = rep(Expr, CG1),
        {named_fun, FunLine, Atom, Clauses};

      _ -> rep(Expr, CG)
    end,

    {map_field_assoc, Line, eabs(list_to_atom(Name), Line), ExprRep}
  end, Inits),

  Line = ?START_LINE(Loc),
  MapRep = {map, Line, PairsRep},
  case maps:find(Ref, CG#cg.ctx#ctx.ref_ts) of
    {ok, T} when element(1, T) == con; element(1, T) == gen ->
      Con = element(2, T),
      IDAtom = id_atom(Con, CG),
      {tuple, Line, [eabs(IDAtom, Line), MapRep]};

    _ -> {tuple, Line, [eabs('%Record', Line), MapRep]}
  end;

rep({anon_record_ext, Loc, Ref, Expr, AllInits}, CG) ->
  ExprRep = rep(Expr, CG),
  ExprLine = element(2, ExprRep),
  ExprMapRep = call(erlang, element, [eabs(2, ExprLine), ExprRep], ExprLine),

  Inits = lists:map(fun(InitOrExt) ->
    setelement(1, InitOrExt, init)
  end, AllInits),

  {tuple, Line, [IDRep, ExtMapRep]} = rep({anon_record, Loc, Ref, Inits}, CG),
  {tuple, Line, [IDRep, call(maps, merge, [ExprMapRep, ExtMapRep], Line)]};

rep({record, Loc, {con_token, _, RawCon}, Inits}, CG) ->
  {tuple, Line, [_, MapRep]} = rep({anon_record, Loc, none, Inits}, CG),
  IDRep = eabs(id_atom(RawCon, CG), Line),
  {tuple, Line, [IDRep, MapRep]};

rep({record_ext, Loc, {con_token, _, RawCon}, Expr, AllInits}, CG) ->
  AnonRecordExt = {anon_record_ext, Loc, none, Expr, AllInits},
  {tuple, Line, [_, MapRep]} = rep(AnonRecordExt, CG),
  IDRep = eabs(id_atom(RawCon, CG), Line),
  {tuple, Line, [IDRep, MapRep]};

rep({field_fn, _, {var, Loc, Name}}, _) ->
  Line = ?START_LINE(Loc),
  RecordRep = {var, Line, 'Record'},
  MapRep = call(erlang, element, [eabs(2, Line), RecordRep], Line),

  AtomRep = eabs(list_to_atom(Name), Line),
  Body = [call(maps, get, [AtomRep, MapRep], Line)],
  Clause = {clause, Line, [RecordRep], [], Body},
  {'fun', Line, {clauses, [Clause]}};

% N can be var_value if we're called by rep({var_value, _, _}, _) above
rep({field, Loc, Expr, {N, _, Name}}, CG) when N == var; N == con_token ->
  Line = ?START_LINE(Loc),
  case Expr of
    {con_token, _, Module} ->
      Mod = list_to_atom(Module),
      case maps:get({Module, Name}, CG#cg.env) of
        % global variable handled by the global manager
        {{global, Atom}, _} -> call(Mod, Atom, [], Line);
        {{option, IDAtom, Key}, _} ->
          {tuple, Line, [eabs(IDAtom, Line), {atom, Line, Key}]};
        {{option, _, _, Atom}, Arity} ->
          Fn = {function, eabs(Mod, Line), eabs(Atom, Line), eabs(Arity, Line)},
          {'fun', Line, Fn};
        {{global_fn, Atom}, Arity} ->
          Fn = {function, eabs(Mod, Line), eabs(Atom, Line), eabs(Arity, Line)},
          {'fun', Line, Fn}
      end;

    _ ->
      ExprRep = rep(Expr, CG),
      MapRep = call(erlang, element, [eabs(2, Line), ExprRep], Line),
      AtomRep = eabs(list_to_atom(Name), Line),
      call(maps, get, [AtomRep, MapRep], Line)
  end;

rep({app, _, {con_token, Loc, Name}, Args}, #cg{in_pattern=true}=CG) ->
  {{option, IDAtom, Key, _}, _} = env_get(Name, CG),
  ArgsRep = lists:map(fun(Arg) -> rep(Arg, CG) end, Args),

  Line = ?START_LINE(Loc),
  % It's possible that this is actually a partial application, but we can't
  % successfully pattern match a newly generated function anyway, so as long as
  % our pattern fails (which it will, because a function won't match a tuple),
  % we're good.
  {tuple, Line, [eabs(IDAtom, Line), {atom, Line, Key} | ArgsRep]};

rep({app, _, {field, Loc, {con_token, _, Module}, {con_token, _, Name}}, Args},
    #cg{in_pattern=true}=CG) ->
  {{option, IDAtom, Key, _}, _} = maps:get({Module, Name}, CG#cg.env),
  ArgsRep = lists:map(fun(Arg) -> rep(Arg, CG) end, Args),

  Line = ?START_LINE(Loc),
  % It's possible that this is actually a partial application, but we can't
  % successfully pattern match a newly generated function anyway, so as long as
  % our pattern fails (which it will, because a function won't match a tuple),
  % we're good.
  {tuple, Line, [eabs(IDAtom, Line), {atom, Line, Key} | ArgsRep]};

rep({app, Loc, Expr, RawArgs}, CG) ->
  ExprRep = rep(Expr, CG),
  Line = ?START_LINE(Loc),

  Arity = arity(Expr, CG),
  Args = case Arity of
    0 ->
      {unit, _} = hd(RawArgs),
      tl(RawArgs);
    _ -> RawArgs
  end,
  NumArgs = length(Args),

  if
    Arity == unknown ->
      ArgsListRep = rep({list, Loc, Args}, CG),
      excluder_remove('_@curry'),
      {call, Line, {atom, Line, '_@curry'},
        [ExprRep, ArgsListRep, {integer, Line, Line}]};

    NumArgs < Arity ->
      NewArgsRep = lists:map(fun(_) ->
        {var, Line, unique("_@Arg")}
      end, lists:seq(NumArgs + 1, Arity)),

      ArgsListRep = rep({list, Loc, Args}, CG),
      NewArgsListRep = lists:foldr(fun(ArgRep, ListRep) ->
        {cons, Line, ArgRep, ListRep}
      end, {nil, Line}, NewArgsRep),

      Body = [{call, Line,
        {remote, Line, {atom, Line, erlang}, {atom, Line, apply}},
        [ExprRep, {op, Line, '++', ArgsListRep, NewArgsListRep}]}],
      Clause = {clause, Line, NewArgsRep, [], Body},
      {'fun', Line, {clauses, [Clause]}};

    NumArgs >= Arity ->
      ImmArgs = lists:sublist(Args, Arity),
      ImmArgsRep = lists:map(fun(Arg) -> rep(Arg, CG) end, ImmArgs),

      Call = case ExprRep of
        {'fun', _, {function, Atom, _}} ->
          {call, Line, {atom, Line, Atom}, ImmArgsRep};
        _ -> {call, Line, ExprRep, ImmArgsRep}
      end,

      if
        NumArgs == Arity -> Call;
        true ->
          RestArgs = lists:sublist(Args, Arity + 1, NumArgs),
          RestArgsListRep = rep({list, Loc, RestArgs}, CG),
          excluder_remove('_@curry'),
          {call, Line, {atom, Line, '_@curry'},
            [Call, RestArgsListRep, {integer, Line, Line}]}
      end
  end;

rep({native, _, {atom, Loc, Mod}, {var, _, Name}, Arity}, _) ->
  Line = ?START_LINE(Loc),
  Atom = list_to_atom(Name),
  {'fun', Line,
    {function, {atom, Line, Mod}, {atom, Line, Atom}, {integer, Line, Arity}}};

rep({'if', Loc, Cond, Then, Else}, CG) ->
  Line = ?START_LINE(Loc),
  ThenBody = case Else of
    {unit, _} -> [rep(Then, CG), eabs({}, Line)];
    _ -> [rep(Then, CG)]
  end,

  % must factor out cond into its own variable, since it might not be a valid
  % guard clause; TODO: optimize by not doing this if valid guard
  CondLine = ?START_LINE(?LOC(Cond)),
  CondVar = {var, CondLine, unique("_@Cond")},
  Match = {match, CondLine, CondVar, rep(Cond, CG)},

  ElseClause = {clause, Line, [], [[{atom, Line, true}]], [rep(Else, CG)]},
  Clauses = [{clause, Line, [], [[CondVar]], ThenBody}, ElseClause],
  {block, Line, [Match, {'if', Line, Clauses}]};

rep({'let', Loc, Bindings, Then}, CG) ->
  {InitsRep, CG1} = lists:mapfoldl(fun({binding, _, Pattern, Expr}, FoldCG) ->
    {PatternRep, ExprRep, FoldCG1} = rep_pattern(Pattern, Expr, FoldCG),
    {{match, element(2, PatternRep), PatternRep, ExprRep}, FoldCG1}
  end, CG, Bindings),

  {block, ?START_LINE(Loc), InitsRep ++ [rep(Then, CG1)]};

rep({if_let, Loc, Pattern, Expr, Then, Else}, CG) ->
  Line = ?START_LINE(Loc),
  {PatternRep, ExprRep, CG1} = rep_pattern(Pattern, Expr, CG),
  ThenBody = case Else of
    {unit, _} -> [rep(Then, CG1), eabs({}, Line)];
    _ -> [rep(Then, CG1)]
  end,

  CaseClauses = [
    {clause, Line, [PatternRep], [], ThenBody},
    {clause, Line, [{var, Line, '_'}], [], [rep(Else, CG)]}
  ],
  {'case', Line, ExprRep, CaseClauses};

rep({match, Loc, Expr, Cases}, CG) ->
  ExprRep = rep(Expr, CG),
  CaseClauses = lists:map(fun({'case', _, Pattern, Then}) ->
    % TODO: use arity(Expr) in case of simple pattern?
    CG1 = gb_sets:fold(fun(Name, FoldCG) ->
      bind(Name, unknown, FoldCG)
    end, CG, type_system:pattern_names(Pattern)),

    PatternRep = rep(Pattern, CG1#cg{in_pattern=true}),
    Body = [rep(Then, CG1)],
    {clause, element(2, PatternRep), [PatternRep], [], Body}
  end, Cases),

  {'case', ?START_LINE(Loc), ExprRep, CaseClauses};

rep({block, Loc, Exprs}, CG) ->
  {block, ?START_LINE(Loc), lists:map(fun(E) -> rep(E, CG) end, Exprs)};

rep({binary_op, Loc, Op, Left, Right}, CG) ->
  Line = ?START_LINE(Loc),
  LeftRep = rep(Left, CG),
  RightRep = rep(Right, CG),

  case Op of
    '++' ->
      excluder_remove('_@concat'),
      {call, Line, {atom, Line, '_@concat'}, [LeftRep, RightRep]};
    '--' ->
      excluder_remove('_@separate'),
      {call, Line, {atom, Line, '_@separate'}, [LeftRep, RightRep]};
    '|>' ->
      case Right of
        {app, Expr, Args} -> rep({app, Loc, Expr, [Left | Args]}, CG);
        _ -> rep({app, Loc, Right, [Left]}, CG)
      end;
    _ ->
      Atom = case Op of
        '==' -> '==';
        '!=' -> '/=';
        '||' -> 'orelse';
        '&&' -> 'andalso';
        '>' -> '>';
        '<' -> '<';
        '>=' -> '>=';
        '<=' -> '=<';
        '+' -> '+';
        '-' -> '-';
        '*' -> '*';
        '/' -> '/';
        '%' -> 'rem'
      end,
      {op, Line, Atom, LeftRep, RightRep}
  end;

rep({unary_op, Loc, Op, Expr}, CG) ->
  Line = ?START_LINE(Loc),
  ExprRep = rep(Expr, CG),

  case Op of
    '!' -> {op, Line, 'not', ExprRep};
    '#' ->
      Call = call(gb_sets, from_list, [ExprRep], Line),
      {tuple, Line, [eabs('%Set', Line), Call]};
    % $ used by the type system to treat Char as Int, but they're the same
    '$' -> ExprRep;
    '-' -> {op, Line, '-', ExprRep};
    'discard' -> {block, Line, [ExprRep, eabs({}, Line)]}
  end.

% recursive definitions allowed for simple pattern functions
rep_pattern({var, _, Name}=Pattern, {fn, _, Args, _}=Expr, CG) ->
  CG1 = bind(Name, length(Args), CG),
  PatternRep = rep(Pattern, CG1#cg{in_pattern=true}),

  % We're unsure whether the named fun is going to be used (i.e. whether the
  % named fun is recursive), so we give it a name prefixed with an underscore
  % to prevent unused errors.
  Atom = unique([$_ | Name]),
  CG2 = env_set(Name, {Atom, length(Args)}, CG1),

  {'fun', FunLine, {clauses, Clauses}} = rep(Expr, CG2),
  NamedFun = {named_fun, FunLine, Atom, Clauses},

  % Use CG1, not CG2, as the named fun is not accessible to the outer scope.
  {PatternRep, NamedFun, CG1};

rep_pattern(Pattern, Expr, CG) ->
  % TODO arity(Expr) for simple patterns
  CG1 = gb_sets:fold(fun(Name, FoldCG) ->
    bind(Name, unknown, FoldCG)
  end, CG, type_system:pattern_names(Pattern)),
  {rep(Pattern, CG1#cg{in_pattern=true}), rep(Expr, CG), CG1}.

rep_init_fn(#comp{module=Module, ast={module, _, _, _, Defs}, deps=Deps}) ->
  ArgVar = {var, 1, unique("_@Arg")},
  ModuleRep = eabs(Module, 1),
  IsMemberCall = call(gb_sets, is_member, [ModuleRep, ArgVar], 1),

  InitSetVar = {var, 1, unique("_@InitSet")},
  MatchAddCall = {match, 1, InitSetVar,
    call(gb_sets, add, [ModuleRep, ArgVar], 1)},

  StartGm = {call, 1, {atom, 1, '_@gm_spawn'}, [{atom, 1, gm(Module)}]},
  InitCalls = lists:map(fun({DepModule, _}) ->
    call(list_to_atom(DepModule), '_@init', [InitSetVar], 1)
  end, Deps),

  GlobalVarNames = lists:filtermap(fun
    ({global, _, _, {fn, _, _, _}, _}) -> false;
    ({global, _, {var, _, Name}, _, _}) -> {true, Name};
    (_) -> false
  end, Defs),
  GlobalCalls = lists:map(fun(Name) ->
    {call, 1, {atom, 1, list_to_atom(Name)}, []}
  end, GlobalVarNames),

  Body = lists:append([
    [MatchAddCall, StartGm],
    InitCalls,
    GlobalCalls,
    [{atom, 1, ok}]
  ]),
  Case = {'case', 1, IsMemberCall, [
    {clause, 1, [{atom, 1, true}], [], [{atom, 1, ok}]},
    {clause, 1, [{atom, 1, false}], [], Body}
  ]},

  % must return ok for module load to succeed
  Clause = {clause, 1, [ArgVar], [], [Case]},
  {function, 1, '_@init', 1, [Clause]}.

eabs(Lit, Line) -> erl_parse:abstract(Lit, Line).
gm(Module) -> list_to_atom(Module ++ "_gm").

env_set(Name, Value, #cg{env=Env, ctx=#ctx{module=Module}}=CG) ->
  Env1 = Env#{{Module, Name} => Value},
  CG#cg{env=Env1}.
env_get(Name, #cg{env=Env, ctx=#ctx{module=Module}}) ->
  maps:get({Module, Name}, Env).

set_module(Module, CG) -> CG#cg{ctx=CG#cg.ctx#ctx{module=Module}}.

arity({fn, _, Args, _}, _) -> length(Args);
arity({binary_op, _, ':', Expr, _}, CG) -> arity(Expr, CG);
arity({N, _, Name}, CG) when N == var; N == con_token ->
  {_, Arity} = env_get(Name, CG),
  Arity;
arity({field_fn, _, _}, _) -> 1;
% TODO: we can figure this out in some cases from typing info or analysis
arity({field, _, _, _}, _) -> unknown;
% TODO: field for module access!!
arity({app, _, Expr, Args}, CG) ->
  case arity(Expr, CG) of
    unknown -> unknown;
    FnArity ->
      Arity = FnArity - length(Args),
      if
        Arity =< 0 -> unknown;
        true -> Arity
      end
  end;
arity({native, _, _, _, Arity}, _) -> Arity;
arity({N, _, _, Then, Else}, CG) when N == 'if'; N == if_let ->
  case Else of
    {unit, _} -> error;
    _ -> case arity(Then, CG) of
      unknown -> arity(Else, CG);
      Arity -> Arity
    end
  end;
arity({'let', _, _, Then}, CG) -> arity(Then, CG);
arity({match, _, _, Cases}, CG) ->
  lists:foldl(fun({_, Expr}, Arity) ->
    case Arity of
      unknown -> arity(Expr, CG);
      _ -> Arity
    end
  end, unknown, Cases);
arity({block, _, Exprs}, CG) -> arity(lists:last(Exprs), CG).

call(Mod, Fn, ArgsRep, Line) ->
  {call, Line, {remote, Line, {atom, Line, Mod}, {atom, Line, Fn}}, ArgsRep}.

bind([H | T]=Name, Arity, CG) ->
  CapName = string:to_upper([H]) ++ T,
  env_set(Name, {unique(CapName), Arity}, CG).

unique(Prefix) -> list_to_atom(unique_name(Prefix)).
unique_name(Prefix) -> lists:concat([Prefix, '@', counter_next()]).

counter_spawn() ->
  case whereis(?COUNTER_NAME) of
    undefined ->
      Pid = spawn(?MODULE, counter_run, [1]),
      register(?COUNTER_NAME, Pid);

    Pid ->
      Pid ! {self(), reset},
      receive
        reset_ok -> true;
        Unexpected ->
          error({"unexpected reset response", Unexpected})
      after 1000 ->
        error("couldn't reset count")
      end
  end.

counter_run(Count) ->
  receive
    {Pid, reset} ->
      Pid ! reset_ok,
      counter_run(1);
    {Pid, next} ->
      Pid ! {next_ok, Count},
      counter_run(Count + 1);
    Unexpected ->
      io:format("unexpected counter message ~p~n", [Unexpected]),
      counter_run(Count)
  end.

counter_next() ->
  ?COUNTER_NAME ! {self(), next},
  receive
    {next_ok, Next} -> Next;
    Unexpected ->
      error({"unexpected next response", Unexpected})
  after 1000 ->
    error("couldn't get next count")
  end.

excluder_spawn(Excluded) ->
  case whereis(?EXCLUDER_NAME) of
    undefined ->
      Pid = spawn(?MODULE, excluder_run, [Excluded]),
      register(?EXCLUDER_NAME, Pid);

    Pid ->
      Pid ! {self(), reset, Excluded},
      receive
        reset_ok -> true;
        Unexpected ->
          error({"unexpected reset response", Unexpected})
      after 1000 ->
        error("couldn't reset excluder")
      end
  end.

excluder_run(Excluded) ->
  receive
    {Pid, reset, NewExcluded} ->
      Pid ! reset_ok,
      excluder_run(NewExcluded);
    {Pid, remove, Element} ->
      Pid ! remove_ok,
      excluder_run(gb_sets:del_element(Element, Excluded));
    {Pid, all} ->
      Pid ! {all_ok, Excluded},
      excluder_run(Excluded);
    Unexpected ->
      io:format("unexpected excluder message ~p~n", [Unexpected]),
      excluder_run(Excluded)
  end.

excluder_remove(Element) ->
  ?EXCLUDER_NAME ! {self(), remove, Element},
  receive
    remove_ok -> ok;
    Unexpected ->
      error({"unexpected remove response", Unexpected})
  after 1000 ->
    error("couldn't remove element from excluder")
  end.

excluder_all() ->
  ?EXCLUDER_NAME ! {self(), all},
  receive
    {all_ok, Excluded} -> Excluded;
    Unexpected ->
      error({"unexpected all response", Unexpected})
  after 1000 ->
    error("couldn't get all excluded elements")
  end.
