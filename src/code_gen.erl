-module(code_gen).
-export([compile_comps/2, counter_run/1, excluder_run/1]).

-include("common.hrl").
-define(COUNTER_NAME, code_gen_counter).
-define(EXCLUDER_NAME, code_gen_excluder).
-define(INIT_FN_ATOM, '_@init').

-record(cg, {env, in_impl = false, ctx}).

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
      {global, _, {var, _, Name}, {fn, _, _, Args, _}, Exported} ->
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

      {enum, _, _, OptionTEs} ->
        {Exports, ModuleCG1} = lists:mapfoldl(fun(OptionTE, FoldCG) ->
          {option, _, {con_token, _, Con}, ArgTEs, KeyNode} = OptionTE,

          Atom = list_to_atom(Con),
          Arity = length(ArgTEs),
          Key = case KeyNode of
            none -> Atom;
            {some, {atom, _, Key_}} -> Key_
          end,

          case Arity of
            0 ->
              Value = {{option, Key}, badarity},
              {[], env_set(Con, Value, FoldCG)};
            _ ->
              Value = {{option, Key, Atom}, Arity},
              {[{Atom, Arity}], env_set(Con, Value, FoldCG)}
          end
        end, ModuleCG, OptionTEs),

        {lists:append(Exports), ModuleCG1};

      {exception, _, {con_token, _, Con}, ArgTEs} ->
        Atom = list_to_atom(Con),
        Arity = length(ArgTEs),
        % Exceptions of the same name in different modules should have different
        % keys, so we qualify Con with the module name.
        Key = list_to_atom(lists:concat([Module, '.', Con])),

        case Arity of
          0 ->
            Value = {{option, Key}, badarity},
            {[], env_set(Con, Value, ModuleCG)};
          _ ->
            Value = {{option, Key, Atom}, Arity},
            {[{Atom, Arity}], env_set(Con, Value, ModuleCG)}
        end;

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

      {interface, _, {con_token, _, RawCon}, _, Fields} ->
        #cg{ctx=#ctx{ifaces=Ifaces}=C} = ModuleCG,
        Con = utils:qualify(RawCon, C),
        {_, FieldTs, _} = maps:get(Con, Ifaces),

        lists:mapfoldl(fun({Sig, RawT}, FoldCG) ->
          {sig, _, {var, _, Name}, _} = Sig,
          Atom = list_to_atom(Name),
          ArgsIVs = utils:args_ivs(RawT),

          % To disambiguate which impl we're using, we need all args up until
          % the first one that contains the target type T, inclusive.
          UntilTargetT = lists:takewhile(fun(IVs) ->
            lists:all(fun({_, V}) -> V /= "T" end, IVs)
          end, ArgsIVs),
          Arity = length(UntilTargetT) + 1,

          Value = {{global_fn, Atom}, Arity},
          {{Atom, Arity}, env_set(Name, Value, FoldCG)}
        end, ModuleCG, lists:zip(Fields, FieldTs));

      {impl, _, Ref, {con_token, _, RawCon}, _, _} ->
        #cg{ctx=#ctx{impls=Impls, impl_refs=ImplRefs}=C} = ModuleCG,
        Con = utils:resolve_con(RawCon, C),
        Key = maps:get(Ref, ImplRefs),
        {_, InstT, _, _} = maps:get(Key, maps:get(Con, Impls)),

        Name = impl_name(Con, Key),
        Atom = list_to_atom(Name),
        Arity = length(utils:ivs(InstT)),

        Value = case Arity of
          0 -> {{global, Atom}, badarity};
          _ -> {{global_fn, Atom}, Arity}
        end,

        ModuleCG1 = env_set(Name, Value, ModuleCG),
        {[{Atom, Arity}], ModuleCG1};

      _ -> {[], ModuleCG}
    end
  end, set_module(Module, CG), Defs).

impl_name(I, Key) -> lists:concat(["_@impl@", I, [$@ | Key]]).
bound_impl_name(I, V) -> lists:concat(["_@bound_impl@", I, [$@ | V]]).

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
          {OptionNames, _, _} = maps:get(Con, Enums),

          lists:foldl(fun(OptionName, FoldCG) ->
            {_, Arity} = maps:get({DepModule, OptionName}, FoldCG#cg.env),
            env_set(OptionName, {{external, DepModule}, Arity}, FoldCG)
          end, NestedCG, OptionNames)
      end
    end, ModuleCG, Idents)
  end, set_module(Module, CG), Deps).

compile_ast(Comp, Exports, CG) ->
  #comp{module=Module, ast=Ast, path=Path} = Comp,
  counter_spawn(),
  excluder_spawn(gb_sets:from_list([
    '_@gm_find',
    '_@gm_set',
    '_@curry',
    '_@wrap_with_impls',
    '_@wrap_with_impls_r',
    '_@concat',
    '_@separate'
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
    {fn, _, _, Args, _} ->
      {'fun', _, {clauses, Clauses}} = rep(Expr, CG),
      {function, Line, list_to_atom(Name), length(Args), Clauses};

    _ ->
      {{global, Atom}, _} = env_get(Name, CG),
      Body = [rep_gm_cache(Atom, rep(Expr, CG), Line, CG)],
      Clause = {clause, Line, [], [], Body},
      {function, Line, list_to_atom(Name), 0, [Clause]}
  end;

rep({enum, _, _, OptionTEs}, _) ->
  FnOptionTEs = lists:filter(fun({option, _, _, ArgTEs, _}) ->
    length(ArgTEs) > 0
  end, OptionTEs),

  lists:map(fun({option, _, {con_token, ConLoc, Con}, ArgTEs, KeyNode}) ->
    Line = ?START_LINE(ConLoc),
    ArgsRep = lists:map(fun(_) -> {var, Line, unique("_@Arg")} end, ArgTEs),

    ConAtom = list_to_atom(Con),
    {KeyLine, Key} = case KeyNode of
      none -> {Line, ConAtom};
      {some, {atom, KeyLoc, Key_}} -> {?START_LINE(KeyLoc), Key_}
    end,

    Body = [{tuple, Line, [{atom, KeyLine, Key} | ArgsRep]}],
    Clause = {clause, Line, ArgsRep, [], Body},
    {function, Line, ConAtom, length(ArgTEs), [Clause]}
  end, FnOptionTEs);

rep({exception, _, {con_token, Loc, Con}, ArgTEs}, CG) ->
  case length(ArgTEs) of
    0 -> [];
    Arity ->
      Line = ?START_LINE(Loc),
      ArgsRep = lists:map(fun(_) -> {var, Line, unique("_@Arg")} end, ArgTEs),

      Atom = list_to_atom(Con),
      % Exceptions of the same name in different modules should have different
      % keys, so we qualify Con with the module name.
      Key = list_to_atom(lists:concat([CG#cg.ctx#ctx.module, '.', Con])),

      Body = [{tuple, Line, [{atom, Line, Key} | ArgsRep]}],
      Clause = {clause, Line, ArgsRep, [], Body},
      {function, Line, Atom, Arity, [Clause]}
  end;

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
  Body = [rep({map, Loc, Pairs}, CG1)],

  Clause = {clause, Line, ArgsRep, [], Body},
  {function, Line, list_to_atom(Con), length(FieldTEs), [Clause]};

rep({interface, _, {con_token, _, RawCon}, _, Fields}, CG) ->
  #cg{ctx=#ctx{
    ifaces=Ifaces,
    inst_refs=InstRefs,
    fn_refs=FnRefs
  }=C} = CG,

  Con = utils:qualify(RawCon, C),
  {_, FieldTs, _} = maps:get(Con, Ifaces),

  lists:map(fun({Sig, RawT}) ->
    {sig, Loc, {var, _, Name}, _} = Sig,
    AllArgsIVs = utils:args_ivs(RawT),

    {ArgsIVsRev, _} = lists:foldl(fun(IVs, {FoldArgsIVs, Done}) ->
      case Done of
        true -> {FoldArgsIVs, Done};
        false ->
          NewDone = lists:any(fun({_, V}) -> V == "T" end, IVs),
          {[IVs | FoldArgsIVs], NewDone}
      end
    end, {[], false}, AllArgsIVs),
    ArgsIVs = lists:reverse(ArgsIVsRev),
    Arity = length(ArgsIVs),

    Args = lists:map(fun(Num) ->
      {var, Loc, lists:concat(["Arg", Num])}
    end, lists:seq(1, Arity)),

    RecordVar = {var, Loc, bound_impl_name(Con, "T")},
    Field = {field, Loc, RecordVar, {var, Loc, Name}},

    InstRef = make_ref(),
    FnRef = make_ref(),
    SubbedVs = lists:foldl(fun(IVs, Memo) ->
      lists:foldl(fun({Is, V}, FoldSubbedVs) ->
        case V of
          % We don't want to pass T's impl to the impl functions; they assume
          % T has been replaced with the instance type. Hence, we omit T from
          % SubbedVs.
          "T" -> FoldSubbedVs;

          % V's impl is in the environment as an argument to the iface function.
          % Hence, we specify the full TV to use the bound impl.
          _ -> FoldSubbedVs#{V => {tv, V, Is, false}}
        end
      end, Memo, IVs)
    end, #{}, ArgsIVs),

    C1 = C#ctx{
      inst_refs=InstRefs#{InstRef => {RawT, SubbedVs}},
      fn_refs=FnRefs#{FnRef => ArgsIVs}
    },
    CG1 = CG#cg{ctx=C1},

    FnName = "Fn",
    App = {app, Loc, {var_ref, Loc, InstRef, FnName}, Args},
    Let = {'let', Loc, [{binding, Loc, {var, Loc, FnName}, Field}], App},
    Fn = {fn, Loc, FnRef, Args, Let},
    rep({global, Loc, {var, Loc, Name}, Fn, true}, CG1)
  end, lists:zip(Fields, FieldTs));

rep({impl, _, Ref, {con_token, _, RawCon}, _, _}, CG) ->
  #cg{ctx=#ctx{
    impls=Impls,
    impl_refs=ImplRefs,
    inst_refs=InstRefs
  }=C} = CG,

  Con = utils:resolve_con(RawCon, C),
  Key = maps:get(Ref, ImplRefs),
  {_, ImplT, Inits, _} = maps:get(Key, maps:get(Con, Impls)),

  {init, Loc, _, _} = hd(Inits),
  Line = ?START_LINE(Loc),

  {ArgsRep, CG1} = case utils:ivs(ImplT) of
    [] -> {[], CG};
    IVs ->
      lists:foldl(fun({Is, V}, {FoldArgsRep, FoldCG}) ->
        gb_sets:fold(fun(I, {NestedArgsRep, NestedCG}) ->
          ImplName = bound_impl_name(I, V),
          NewCG = bind(ImplName, badarity, NestedCG),
          {ImplAtom, _} = env_get(ImplName, NewCG),
          {[{var, Line, ImplAtom} | NestedArgsRep], NewCG}
        end, {FoldArgsRep, FoldCG}, Is)
      end, {[], CG}, IVs)
  end,

  RecordRep = rep({anon_record, Loc, Inits}, CG1#cg{in_impl=true}),
  Body = case maps:find(Ref, InstRefs) of
    error -> [RecordRep];
    {ok, {T, SubbedVs}} ->
      Result = rep_impls(utils:ivs(T), Loc, #{}, SubbedVs, CG1),
      {[], ImplReps, BindMap, _} = Result,

      MergedRep = lists:foldl(fun(ImplRep, FoldMergedRep) ->
        call(maps, merge, [ImplRep, FoldMergedRep], Line)
      end, RecordRep, ImplReps),

      maps:fold(fun(Atom, ValueRep, FoldBody) ->
        [{match, Line, {var, Line, Atom}, ValueRep} | FoldBody]
      end, [MergedRep], BindMap)
  end,

  ImplAtom = list_to_atom(impl_name(Con, Key)),
  FinalBody = case ArgsRep of
    [] -> [rep_gm_cache(ImplAtom, {block, Line, Body}, Line, CG1)];
    _ -> Body
  end,

  Clause = {clause, Line, ArgsRep, [], FinalBody},
  {function, Line, ImplAtom, length(ArgsRep), [Clause]};

rep({sig, _, _, _}, _) -> [];

rep({fn, Loc, Ref, Args, Expr}, CG) ->
  Names = gb_sets:union(lists:map(fun type_system:pattern_names/1, Args)),
  CG1 = gb_sets:fold(fun(Name, FoldCG) ->
    bind(Name, unknown, FoldCG)
  end, CG, Names),

  % length(AllArgsIVs) can be greater than length(Args) if this fn returns
  % another fn. We only need to process this fn's args here, so clamp.
  AllArgsIVs = maps:get(Ref, CG#cg.ctx#ctx.fn_refs),
  ArgsIVs = lists:sublist(AllArgsIVs, length(Args)),

  ArgsRep = lists:map(fun(Pattern) -> rep(Pattern, CG1) end, Args),
  {PatternReps, CG2} = rep_arg_iv_patterns(ArgsRep, ArgsIVs, true, CG1),

  Line = ?START_LINE(Loc),
  Clause = {clause, Line, PatternReps, [], [rep(Expr, CG2)]},
  {'fun', Line, {clauses, [Clause]}};

rep({expr_sig, Loc, Ref, Expr, _}, CG) ->
  Rep = rep(Expr, CG),
  rewrite_ref(Rep, Ref, Loc, CG);

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
    {{option, Key}, _} -> {atom, Line, Key};
    {{option, _, Atom}, Arity} -> {'fun', Line, {function, Atom, Arity}};
    {{global_fn, Atom}, Arity} -> {'fun', Line, {function, Atom, Arity}};
    {{external, Module}, _} ->
      Mod = list_to_atom(Module),
      case maps:get({Module, Name}, CG#cg.env) of
        % global variable handled by the global manager
        {{global, Atom}, _} -> call(Mod, Atom, [], Line);
        {{option, Key}, _} -> {atom, Line, Key};
        {{option, _, Atom}, Arity} ->
          Fn = {function, eabs(Mod, Line), eabs(Atom, Line), eabs(Arity, Line)},
          {'fun', Line, Fn};
        {{global_fn, Atom}, Arity} ->
          Fn = {function, eabs(Mod, Line), eabs(Atom, Line), eabs(Arity, Line)},
          {'fun', Line, Fn}
      end;
    {Atom, _} when is_atom(Atom) -> {var, Line, Atom}
  end;

rep({var_ref, Loc, Ref, Name}, CG) ->
  Rep = rep({var, Loc, Name}, CG),
  rewrite_ref(Rep, Ref, Loc, CG);

rep({anon_record, Loc, Inits}, CG) ->
  PairsRep = lists:map(fun({init, _, {var, VarLoc, Name}, Expr}) ->
    Line = ?START_LINE(VarLoc),

    ExprRep = case Expr of
      {fn, _, _, Args, _} ->
        case CG#cg.in_impl of
          false ->
            % We're unsure whether the named fun is going to be used (i.e.
            % whether the named fun is recursive), so we give it a name prefixed
            % with an underscore to prevent unused errors.
            Atom = unique([$_ | Name]),
            CG1 = env_set(Name, {Atom, length(Args)}, CG),

            {'fun', FunLine, {clauses, Clauses}} = rep(Expr, CG1),
            {named_fun, FunLine, Atom, Clauses};

          true ->
            % We can't used a named fun in this case, since recursive calls
            % should use the global iface function.
            %
            % Also, any nested records can still be recursive, so unset in_impl.
            CG1 = CG#cg{in_impl=false},
            rep(Expr, CG1)
        end;

      _ -> rep(Expr, CG)
    end,

    {map_field_assoc, Line, eabs(list_to_atom(Name), Line), ExprRep}
  end, Inits),

  {map, ?START_LINE(Loc), PairsRep};

rep({anon_record_ext, Loc, Expr, AllInits}, CG) ->
  ExprRep = rep(Expr, CG),
  Inits = lists:map(fun(InitOrExt) ->
    setelement(1, InitOrExt, init)
  end, AllInits),
  ExtRep = rep({anon_record, Loc, Inits}, CG),
  call(maps, merge, [ExprRep, ExtRep], ?START_LINE(Loc));

rep({record, Loc, _, Inits}, CG) -> rep({anon_record, Loc, Inits}, CG);

rep({record_ext, Loc, _, Expr, AllInits}, CG) ->
  rep({anon_record_ext, Loc, Expr, AllInits}, CG);

rep({field_fn, _, {var, Loc, Name}}, _) ->
  Line = ?START_LINE(Loc),
  RecordRep = {var, Line, unique("_@Record")},
  AtomRep = eabs(list_to_atom(Name), Line),

  Body = [call(maps, get, [AtomRep, RecordRep], Line)],
  Clause = {clause, Line, [RecordRep], [], Body},
  {'fun', Line, {clauses, [Clause]}};

% N can be var_value if we're called by rep({var_value, _, _}, _) above
rep({field, Loc, Expr, Prop}, CG) ->
  Line = ?START_LINE(Loc),
  case Expr of
    {con_token, _, Module} ->
      Name = case Prop of
        {var_ref, _, _, Name_} -> Name_;
        {con_token, _, Name_} -> Name_
      end,

      {_, Arity} = maps:get({Module, Name}, CG#cg.env),
      CG1 = env_set(Name, {{external, Module}, Arity}, CG),
      rep(Prop, CG1);

    _ ->
      ExprRep = rep(Expr, CG),
      {var, _, Name} = Prop,
      AtomRep = eabs(list_to_atom(Name), Line),
      call(maps, get, [AtomRep, ExprRep], Line)
  end;

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

rep({variant, _, {con_token, Loc, Name}, Args}, CG) ->
  Key = option_key(Name, CG),
  ArgsRep = lists:map(fun(Arg) -> rep(Arg, CG) end, Args),

  Line = ?START_LINE(Loc),
  case ArgsRep of
    [] -> {atom, Line, Key};
    _ -> {tuple, Line, [{atom, Line, Key} | ArgsRep]}
  end;

rep({variant, _, Field, Args}, CG) ->
  {field, Loc, {con_token, _, Module}, {con_token, _, Name}} = Field,
  Key = option_key(Module, Name, CG),
  ArgsRep = lists:map(fun(Arg) -> rep(Arg, CG) end, Args),

  Line = ?START_LINE(Loc),
  case ArgsRep of
    [] -> {atom, Line, Key};
    _ -> {tuple, Line, [{atom, Line, Key} | ArgsRep]}
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

    PatternRep = rep(Pattern, CG1),
    Body = [rep(Then, CG1)],
    {clause, element(2, PatternRep), [PatternRep], [], Body}
  end, Cases),

  {'case', ?START_LINE(Loc), ExprRep, CaseClauses};

rep({'try', Loc, Expr, Cases}, CG) ->
  ExprRep = rep(Expr, CG),
  CatchClauses = lists:map(fun({'case', _, Pattern, Then}) ->
    % TODO: use arity(Expr) in case of simple pattern?
    CG1 = gb_sets:fold(fun(Name, FoldCG) ->
      bind(Name, unknown, FoldCG)
    end, CG, type_system:pattern_names(Pattern)),

    Line = ?START_LINE(element(2, Pattern)),
    PatternRep = {tuple, Line, [
      eabs(throw, Line),
      rep(Pattern, CG1),
      {var, Line, '_'}
    ]},

    Body = [rep(Then, CG1)],
    {clause, Line, [PatternRep], [], Body}
  end, Cases),

  {'try', ?START_LINE(Loc), [ExprRep], [], CatchClauses, []};

rep({'ensure', Loc, Expr, After}, CG) ->
  ExprRep = rep(Expr, CG),
  AfterRep = rep(After, CG),
  {'try', ?START_LINE(Loc), [AfterRep], [], [], [ExprRep]};

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
    '#' -> call(gb_sets, from_list, [ExprRep], Line);
    % $ used by the type system to treat Char as Int, but they're the same
    '$' -> ExprRep;
    '-' -> {op, Line, '-', ExprRep};
    'raise' -> call(erlang, throw, [ExprRep], Line);
    'discard' -> {block, Line, [ExprRep, eabs({}, Line)]}
  end.

% recursive definitions allowed for simple pattern functions
rep_pattern({var, _, Name}=Pattern, {fn, _, _, Args, _}=Expr, CG) ->
  CG1 = bind(Name, length(Args), CG),
  PatternRep = rep(Pattern, CG1),

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
  {rep(Pattern, CG1), rep(Expr, CG), CG1}.

rep_init_fn(#comp{module=Module, ast={module, _, _, _, Defs}, deps=Deps}) ->
  ArgVar = {var, 1, unique("_@Arg")},
  ModuleRep = eabs(Module, 1),
  IsMemberCall = call(gb_sets, is_member, [ModuleRep, ArgVar], 1),

  InitSetVar = {var, 1, unique("_@InitSet")},
  MatchAddCall = {match, 1, InitSetVar,
    call(gb_sets, add, [ModuleRep, ArgVar], 1)},

  StartGm = {call, 1, {atom, 1, '_@gm_spawn'}, [{atom, 1, gm(Module)}]},
  InitCalls = lists:map(fun({DepModule, _}) ->
    call(list_to_atom(DepModule), ?INIT_FN_ATOM, [InitSetVar], 1)
  end, Deps),

  GlobalVarNames = lists:filtermap(fun
    ({global, _, _, {fn, _, _, _, _}, _}) -> false;
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
  {function, 1, ?INIT_FN_ATOM, 1, [Clause]}.

rep_arg_iv_patterns(ArgsRep, ArgsIVs, Bind, CG) ->
  {PatternReps, {_, CG1}} = lists:mapfoldl(fun({PatternRep, IVs}, OuterMemo) ->
    {SeenVs, OuterCG} = OuterMemo,
    PatternLine = element(2, PatternRep),

    {ImplReps, NewSeenVs, NewOuterCG} = lists:foldl(fun({Is, V}, Memo) ->
      {FoldImplReps, FoldSeenVs, FoldCG} = Memo,
      case gb_sets:is_member(V, FoldSeenVs) of
        true -> Memo;
        false ->
          {NewImplReps, NewCG} = gb_sets:fold(fun(I, NestedMemo) ->
            {NestedImplReps, NestedCG} = NestedMemo,
            ImplName = bound_impl_name(I, V),

            case Bind of
              true ->
                NestedCG1 = bind(ImplName, badarity, NestedCG),
                {ImplAtom, _} = env_get(ImplName, NestedCG1),
                ImplRep = {var, PatternLine, ImplAtom},
                {[ImplRep | NestedImplReps], NestedCG1};

              false ->
                ImplRep = {var, PatternLine, list_to_atom(ImplName)},
                {[ImplRep | NestedImplReps], NestedCG}
            end
          end, {FoldImplReps, FoldCG}, Is),

          {NewImplReps, gb_sets:add(V, FoldSeenVs), NewCG}
      end
    end, {[], SeenVs, OuterCG}, IVs),

    FinalPatternRep = case ImplReps of
      [] -> PatternRep;
      _ -> {tuple, PatternLine, [PatternRep | ImplReps]}
    end,

    {FinalPatternRep, {NewSeenVs, NewOuterCG}}
  end, {gb_sets:new(), CG}, lists:zip(ArgsRep, ArgsIVs)),

  {PatternReps, CG1}.

rep_gm_cache(Atom, Rep, Line, CG) ->
  Gm = gm(CG#cg.ctx#ctx.module),
  excluder_remove('_@gm_find'),
  excluder_remove('_@gm_set'),

  FindCall = {call, Line, {atom, Line, '_@gm_find'},
    [{atom, Line, Gm}, {atom, Line, Atom}]},
  SetCall = {call, Line, {atom, Line, '_@gm_set'},
    [{atom, Line, Gm}, {atom, Line, Atom}, Rep]},

  Var = {var, Line, unique("_@Value")},
  {'case', Line, FindCall, [
    {clause, Line, [{tuple, Line, [{atom, Line, ok}, Var]}], [], [Var]},
    {clause, Line, [{atom, Line, error}], [], [SetCall]}
  ]}.

rep_impls(IVs, Loc, BindMap, SubbedVs, CG) ->
  Line = ?START_LINE(Loc),
  #cg{env=Env, ctx=#ctx{
    module=Module,
    nested_ivs=NestedIVs,
    ifaces=Ifaces,
    impls=Impls
  }} = CG,

  {FinalArgIVs, FinalMemo} = lists:mapfoldl(fun({Is, V}, Memo) ->
    {FoldImplReps, FoldBindMap, FoldSubbedVs} = Memo,

    {T, NewV, NewIs} = case maps:find(V, FoldSubbedVs) of
      error -> {none, none, none};
      {ok, {tv, NewV_, NewIs_, _}} -> {none, NewV_, NewIs_};
      {ok, {gen, NewV_, NewIs_, _, _}} -> {none, NewV_, NewIs_};
      {ok, T_} -> {T_, none, none}
    end,

    % V will not be in SubbedVs if it is bound in the env or if it has been seen
    % before. In both these cases, we don't want to add impls.
    case {T, NewV, NewIs} of
      {none, none, none} -> {[], Memo};

      {none, NewV, NewIs} ->
        {FirstI, _} = gb_sets:next(gb_sets:iterator(Is)),
        FirstImplName = bound_impl_name(child_i(FirstI, NewIs, Ifaces), NewV),

        IsBound = maps:is_key({Module, FirstImplName}, Env),
        ArgIVs = if
          IsBound -> [];
          % Not a bound TV, so we must introduce IVs as arguments.
          true -> [{Is, NewV}]
        end,

        {NewImplReps, NewBindMap} = gb_sets:fold(
          fun(I, {NestedImplReps, NestedBindMap}) ->
            ImplName = bound_impl_name(child_i(I, NewIs, Ifaces), NewV),
            ImplAtom = list_to_atom(ImplName),
            ImplRep = {var, Line, ImplAtom},

            NestedBindMap1 = if
              IsBound ->
                NestedBindMap#{ImplAtom => rep({var, Loc, ImplName}, CG)};
              true -> NestedBindMap
            end,
            {[ImplRep | NestedImplReps], NestedBindMap1}
          end,
          {FoldImplReps, FoldBindMap},
          Is
        ),

        NewSubbedVs = maps:remove(V, FoldSubbedVs),
        {ArgIVs, {NewImplReps, NewBindMap, NewSubbedVs}};

      {T, _, _} ->
        Key = utils:impl_key(T),

        Result = gb_sets:fold(fun(I, FoldMemo) ->
          {NestedArgIVs, NestedImplReps, NestedBindMap, NestedSubbedVs} = FoldMemo,
          {_, _, _, ImplModule} = maps:get(Key, maps:get(I, Impls)),
          ImplName = impl_name(I, Key),
          ImplAtom = list_to_atom(ImplName),

          ImplVarCG = case ImplModule of
            Module -> CG;
            _ ->
              {_, Arity} = maps:get({ImplModule, ImplName}, CG#cg.env),
              env_set(ImplName, {{external, ImplModule}, Arity}, CG)
          end,
          NestedBindMap1 = NestedBindMap#{
            ImplAtom => rep({var, Loc, ImplName}, ImplVarCG)
          },
          ImplVarRep = {var, Line, ImplAtom},

          case maps:find({I, V}, NestedIVs) of
            error ->
              NewImplReps = [ImplVarRep | NestedImplReps],
              {NestedArgIVs, NewImplReps, NestedBindMap1, NestedSubbedVs};

            {ok, IVsNested} ->
              {NewArgIVs, ImplArgsRep, NewBindMap, NewSubbedVs} = rep_impls(
                IVsNested,
                Loc,
                NestedBindMap1,
                NestedSubbedVs,
                CG
              ),

              % We don't need to curry here; we know the implementation
              % accepts all arguments directly; i.e. it doesn't return
              % another function that accepts more arguments.
              NewImplRep = {call, Line, ImplVarRep, ImplArgsRep},
              {
                [NewArgIVs | NestedArgIVs],
                [NewImplRep | NestedImplReps],
                NewBindMap,
                NewSubbedVs
              }
          end
        end, {[], FoldImplReps, FoldBindMap, maps:remove(V, FoldSubbedVs)}, Is),

        {ArgIVs, NewImplReps, NewBindMap, NewSubbedVs} = Result,
        {ArgIVs, {NewImplReps, NewBindMap, NewSubbedVs}}
    end
  end, {[], BindMap, SubbedVs}, IVs),

  erlang:insert_element(1, FinalMemo, lists:flatten(FinalArgIVs)).

child_i(TargetI, Is, Ifaces) ->
  gb_sets:fold(fun(I, FoldI) ->
    case FoldI of
      none ->
        case gb_sets:is_member(TargetI, utils:family_is(I, Ifaces)) of
          true -> I;
          false -> FoldI
        end;
      _ -> FoldI
    end
  end, none, Is).

rewrite_ref(Rep, Ref, Loc, CG) ->
  % rewrite() expects a single var rep as a parameter, whereas Rep might be
  % a call or something more complex; store the result.
  Line = ?START_LINE(Loc),
  NewVar = {var, Line, unique("Var")},
  Match = {match, Line, NewVar, Rep},

  InstRefs = CG#cg.ctx#ctx.inst_refs,
  {Stmts, ResultRep} = case maps:find(Ref, InstRefs) of
    {ok, {T, SubbedVs}} -> rewrite(T, NewVar, Loc, SubbedVs, CG);
    error -> {[], Rep}
  end,

  case Stmts of
    [] -> Rep;
    _ -> {block, Line, [Match | Stmts] ++ [ResultRep]}
  end.

rewrite({lam, _, _}=LamT, VarRep, Loc, SubbedVs, CG) ->
  Line = ?START_LINE(Loc),

  % Must fold*l* b/c impls associated with multiple args are passed through the
  % left-most arg.
  {ArgsRepRev, ArgsIVsRev, ImplRepsRev, BindMap, _} = lists:foldl(fun(IVs, Memo) ->
    {FoldArgsRep, FoldArgsIVs, FoldImplReps, FoldBindMap, FoldSubbedVs} = Memo,
    {NewArgIVs, NewImplReps, NewBindMap, NewSubbedVs} = rep_impls(
      IVs,
      Loc,
      FoldBindMap,
      FoldSubbedVs,
      CG
    ),

    NewArgRep = {var, Line, unique("Arg")},
    {
      [NewArgRep | FoldArgsRep],
      [NewArgIVs | FoldArgsIVs],
      [NewImplReps | FoldImplReps],
      NewBindMap,
      NewSubbedVs
    }
  end, {[], [], [], #{}, SubbedVs}, utils:args_ivs(LamT)),

  ArgsRep = lists:reverse(ArgsRepRev),
  ArgsIVs = lists:reverse(ArgsIVsRev),
  ImplReps = lists:reverse(ImplRepsRev),

  {PatternReps, _} = rep_arg_iv_patterns(ArgsRep, ArgsIVs, false, CG),

  case maps:size(BindMap) of
    % If there aren't any bindings, we didn't solve for any impls (both bound
    % impls and solved impls create bindings), so don't rewrite.
    0 -> {[], VarRep};

    _ ->
      BindListRep = maps:fold(fun(Atom, ValueRep, FoldListRep) ->
        TupleRep = {tuple, Line, [eabs(Atom, Line), ValueRep]},
        {cons, Line, TupleRep, FoldListRep}
      end, {nil, Line}, BindMap),

      ResultRep = {var, Line, unique("Lam")},
      excluder_remove('_@wrap_with_impls'),
      excluder_remove('_@wrap_with_impls_r'),

      CallArgsRep = [
        VarRep,
        eabs(PatternReps, Line),
        eabs(ImplReps, Line),
        BindListRep,
        eabs(Line, Line)
      ],
      Call = {call, Line, {atom, Line, '_@wrap_with_impls'}, CallArgsRep},
      {[{match, Line, ResultRep, Call}], ResultRep}
  end;

rewrite({tuple, ElemTs}, VarRep, Loc, SubbedVs, CG) ->
  Line = ?START_LINE(Loc),
  ElemReps = lists:map(fun(Index) ->
    {var, Line, unique(lists:concat(["Elem", Index]))}
  end, lists:seq(1, length(ElemTs))),
  Match = {match, Line, {tuple, Line, ElemReps}, VarRep},

  {NewElemReps, AllStmts} = lists:mapfoldr(fun({ElemT, ElemRep}, FoldStmts) ->
    case rewrite(ElemT, ElemRep, Loc, SubbedVs, CG) of
      {[], _} -> {ElemRep, FoldStmts};
      {Stmts, NewElemRep} -> {NewElemRep, [Stmts | FoldStmts]}
    end
  end, [], lists:zip(ElemTs, ElemReps)),

  case lists:append(AllStmts) of
    [] -> {[], VarRep};
    Stmts ->
      ResultRep = {var, Line, unique("Tuple")},
      TupleRep = {tuple, Line, NewElemReps},
      {[Match | Stmts] ++ [{match, Line, ResultRep, TupleRep}], ResultRep}
  end;

rewrite({gen, {con, "List"}, [ElemT]}, VarRep, Loc, SubbedVs, CG) ->
  Line = ?START_LINE(Loc),
  ElemRep = {var, Line, unique("Elem")},

  case rewrite(ElemT, ElemRep, Loc, SubbedVs, CG) of
    {[], _} -> {[], VarRep};

    {Stmts, NewElemRep} ->
      Body = Stmts ++ [NewElemRep],
      Clause = {clause, Line, [ElemRep], [], Body},
      FunRep = {'fun', Line, {clauses, [Clause]}},

      Call = call(lists, map, [FunRep, VarRep], Line),
      ResultRep = {var, Line, unique("List")},
      {[{match, Line, ResultRep, Call}], ResultRep}
  end;

rewrite({gen, {con, "Set"}, [ElemT]}, VarRep, Loc, SubbedVs, CG) ->
  Line = ?START_LINE(Loc),
  ElemRep = {var, Line, unique("Elem")},

  case rewrite(ElemT, ElemRep, Loc, SubbedVs, CG) of
    {[], _} -> {[], VarRep};

    {Stmts, NewElemRep} ->
      FoldSetRep = {var, Line, unique("FoldSet")},
      AddCall = call(gb_sets, add, [NewElemRep, FoldSetRep], Line),
      Body = Stmts ++ [AddCall],
      Clause = {clause, Line, [ElemRep, FoldSetRep], [], Body},
      FunRep = {'fun', Line, {clauses, [Clause]}},

      NewSetRep = call(gb_sets, new, [], Line),
      FoldCall = call(gb_sets, fold, [FunRep, NewSetRep, VarRep], Line),
      ResultRep = {var, Line, unique("List")},
      {[{match, Line, ResultRep, FoldCall}], ResultRep}
  end;

rewrite({gen, {con, "Map"}, [KeyT, ValueT]}, VarRep, Loc, SubbedVs, CG) ->
  Line = ?START_LINE(Loc),
  KeyRep = {var, Line, unique("Key")},
  ValueRep = {var, Line, unique("Value")},

  {KeyStmts, NewKeyRep} = rewrite(KeyT, KeyRep, Loc, SubbedVs, CG),
  {ValueStmts, NewValueRep} = rewrite(ValueT, ValueRep, Loc, SubbedVs, CG),
  ResultRep = {var, Line, unique("Map")},

  case {KeyStmts, ValueStmts} of
    {[], []} -> {[], VarRep};

    {[], _} ->
      Body = ValueStmts ++ [NewValueRep],
      Clause = {clause, Line, [{var, Line, '_'}, ValueRep], [], Body},
      FunRep = {'fun', Line, {clauses, [Clause]}},
      MapCall = call(maps, map, [FunRep, VarRep], Line),
      {[{match, Line, ResultRep, MapCall}], ResultRep};

    _ ->
      FoldMapRep = {var, Line, unique("FoldMap")},
      AddCall = call(maps, put, [NewKeyRep, NewValueRep, FoldMapRep], Line),
      Body = lists:append([KeyStmts, ValueStmts, [AddCall]]),
      Clause = {clause, Line, [KeyRep, ValueRep, FoldMapRep], [], Body},
      FunRep = {'fun', Line, {clauses, [Clause]}},

      NewMapRep = {map, Line, []},
      FoldCall = call(maps, fold, [FunRep, NewMapRep, VarRep], Line),
      {[{match, Line, ResultRep, FoldCall}], ResultRep}
  end;

rewrite({gen, {con, Con}, ParamTs}=GenT, VarRep, Loc, SubbedVs, CG) ->
  #ctx{aliases=Aliases, structs=Structs, enums=Enums} = CG#cg.ctx,
  IsStruct = maps:is_key(Con, Structs),
  IsEnum = maps:is_key(Con, Enums),

  if
    IsStruct ->
      {record, _, _}=RecordT = utils:unalias(GenT, CG#cg.ctx#ctx.aliases),
      rewrite(RecordT, VarRep, Loc, SubbedVs, CG);

    IsEnum ->
      {_, Vs, GenOptions} = maps:get(Con, Enums),
      Subs = maps:from_list(lists:zip(Vs, ParamTs)),
      Line = ?START_LINE(Loc),

      IsTupleCall = call(erlang, is_tuple, [VarRep], Line),
      ElementCall = call(erlang, element, [eabs(1, Line), VarRep], Line),
      If = {'if', Line, [
        {clause, Line, [], [[IsTupleCall]], [ElementCall]},
        {clause, Line, [], [[eabs(true, Line)]], [VarRep]}
      ]},
      KeyRep = {var, Line, unique("Key")},
      Match = {match, Line, KeyRep, If},

      LastClause = {clause, Line, [{var, Line, '_'}], [], [VarRep]},
      Clauses = lists:foldl(fun({Key, TupleT}, FoldClauses) ->
        SubbedT = utils:subs(TupleT, #sub_opts{subs=Subs, aliases=Aliases}),
        case rewrite(SubbedT, VarRep, Loc, SubbedVs, CG) of
          {[], _} -> FoldClauses;
          {Stmts, NewTupleRep} ->
            Body = Stmts ++ [NewTupleRep],
            [{clause, Line, [eabs(Key, Line)], [], Body} | FoldClauses]
        end
      end, [LastClause], GenOptions),

      case Clauses of
        [LastClause] -> {[], VarRep};
        _ ->
          Case = {'case', Line, KeyRep, Clauses},
          ResultRep = {var, Line, unique("Enum" ++ Con)},
          ResultMatch = {match, Line, ResultRep, Case},
          {[Match, ResultMatch], ResultRep}
      end
  end;

rewrite({record, _, FieldMap}, VarRep, Loc, SubbedVs, CG) ->
  Line = ?START_LINE(Loc),

  {AllStmts, ExactReps, Updates} = maps:fold(fun(Name, FieldT, Memo) ->
    {FoldStmts, FoldExactReps, FoldUpdates} = Memo,
    FieldRep = {var, Line, unique("Field_" ++ Name)},

    case rewrite(FieldT, FieldRep, Loc, SubbedVs, CG) of
      {[], _} -> {FoldStmts, FoldExactReps, FoldUpdates};
      {Stmts, NewFieldRep} ->
        AtomRep = eabs(list_to_atom(Name), Line),
        ExactRep = {map_field_exact, Line, AtomRep, FieldRep},

        NewStmts = [Stmts | FoldStmts],
        NewExactReps = [ExactRep | FoldExactReps],
        NewUpdates = [{Name, NewFieldRep} | FoldUpdates],
        {NewStmts, NewExactReps, NewUpdates}
    end
  end, {[], [], []}, FieldMap),

  Match = {match, Line, {map, Line, ExactReps}, VarRep},
  case lists:append(AllStmts) of
    [] -> {[], VarRep};
    Stmts ->
      UpdateReps = lists:map(fun({Name, NewFieldRep}) ->
        AtomRep = eabs(list_to_atom(Name), Line),
        {map_field_exact, Line, AtomRep, NewFieldRep}
      end, Updates),

      ResultRep = {var, Line, unique("Record")},
      ResultMatch = {match, Line, ResultRep, {map, Line, VarRep, UpdateReps}},
      {[Match | Stmts] ++ [ResultMatch], ResultRep}
  end;

% BaseT (the third element) must be a TV at this point, since this program
% passed type checking.
rewrite({record_ext, A, {tv, _, _, _}, Ext}, VarRep, Loc, SubbedVs, CG) ->
  rewrite({record, A, Ext}, VarRep, Loc, SubbedVs, CG);

% The only way to create a value of type T<A> that is instantiated and needs to
% be rewritten is to call some native erlang function and cast the result.
% The user shouldn't be doing this; it's dangerous and won't work, as no value
% can represent any T<A>. We simply do nothing in this case, and let any
% runtime exceptions take their course.
rewrite({gen, _, _, _, _}, VarRep, _, _, _) -> {[], VarRep};

rewrite({con, _}, VarRep, _, _, _) -> {[], VarRep};
rewrite({tv, _, _, _}, VarRep, _, _, _) -> {[], VarRep};
rewrite(unit, VarRep, _, _, _) -> {[], VarRep}.

option_key(Name, CG) -> option_key(CG#cg.ctx#ctx.module, Name, CG).
option_key(Module, Name, #cg{env=Env}=CG) ->
  case maps:get({Module, Name}, Env) of
    {{external, OtherModule}, _} -> option_key(OtherModule, Name, CG);
    {{option, Key}, _} -> Key;
    {{option, Key, _}, _} -> Key
  end.

eabs(Lit, Line) -> erl_parse:abstract(Lit, Line).
gm(Module) -> list_to_atom(Module ++ "_gm").

env_set(Name, Value, #cg{env=Env, ctx=#ctx{module=Module}}=CG) ->
  Env1 = Env#{{Module, Name} => Value},
  CG#cg{env=Env1}.
env_get(Name, #cg{env=Env, ctx=#ctx{module=Module}}) ->
  maps:get({Module, Name}, Env).

set_module(Module, CG) -> CG#cg{ctx=CG#cg.ctx#ctx{module=Module}}.

arity({fn, _, _, Args, _}, _) -> length(Args);
arity({expr_sig, _, _, Expr, _}, CG) -> arity(Expr, CG);
arity({con_token, _, Name}, CG) ->
  {_, Arity} = env_get(Name, CG),
  Arity;
arity({var_ref, _, _, Name}, CG) ->
  {_, Arity} = env_get(Name, CG),
  Arity;
arity({field_fn, _, _}, _) -> 1;
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
arity({N, _, _, _, _}, _) when N == 'if'; N == if_let -> unknown;
arity({'let', _, _, Then}, CG) -> arity(Then, CG);
arity({match, _, _, _}, _) -> unknown;
arity({'try', _, _, _}, _) -> unknown;
arity({ensure, _, _, After}, CG) -> arity(After, CG);
arity({block, _, Exprs}, CG) -> arity(lists:last(Exprs), CG);
arity({binary_op, Loc, '|>', Left, Right}, CG) ->
  arity({app, Loc, Right, [Left]}, CG);
arity(_, _) -> unknown.

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
