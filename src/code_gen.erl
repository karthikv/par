-module(code_gen).
-export([compile_comps/1, counter_run/1, excluder_run/1]).

-include("errors.hrl").
-define(COUNTER_NAME, code_gen_counter).
-define(EXCLUDER_NAME, code_gen_excluder).
-define(INIT_FN_ATOM, '_@init').

compile_comps(Comps) ->
  {AllExports, Env} = lists:mapfoldl(fun(Comp, FoldEnv) ->
    {Exports, FoldEnv1} = populate_env(Comp, FoldEnv),
    {lists:append(Exports), FoldEnv1}
  end, #{}, Comps),

  FullEnv = lists:foldl(fun populate_direct_imports/2, Env, Comps),

  lists:map(fun({Comp, Exports}) ->
    compile_ast(Comp, Exports, FullEnv)
  end, lists:zip(Comps, AllExports)).

populate_env(#comp{module=Module, ast={module, _, _, _, Defs}}, Env) ->
  % populate env and aggregate exports
  lists:mapfoldl(fun(Node, ModuleEnv) ->
    case Node of
      {global, _, {var, _, Name}, {fn, _, Args, _}, Exported} ->
        Atom = list_to_atom(Name),
        Arity = length(Args),
        Value = {{global_fn, Atom}, Arity},

        ModuleEnv1 = env_set(Name, Value, ModuleEnv),
        if
          Exported or ((Name == "main") and (Arity == 0)) ->
            {[{Atom, Arity}], ModuleEnv1};
          true -> {[], ModuleEnv1}
        end;

      {global, _, {var, _, Name}, _, Exported} ->
        Atom = list_to_atom(Name),
        Value = {{global, Atom}, unknown},

        ModuleEnv1 = env_set(Name, Value, ModuleEnv),
        case Exported of
          true -> {[{Atom, 0}], ModuleEnv1};
          false -> {[], ModuleEnv1}
        end;

      {enum, _, _, OptionTEs} ->
        {EnumExports, ModuleEnv1} = lists:mapfoldl(fun(OptionTE, NestedEnv) ->
          {option, _, {con_token, _, Con}, ArgsTE, KeyNode} = OptionTE,

          Atom = list_to_atom(Con),
          Arity = length(ArgsTE),
          Key = case KeyNode of
            none -> Atom;
            {some, {atom, _, Key_}} -> Key_
          end,

          case Arity of
            0 -> {[], env_set(Con, {{option, Key}, badarity}, NestedEnv)};
            _ ->
              Value = {{option, Key, Atom}, Arity},
              {[{Atom, Arity}], env_set(Con, Value, NestedEnv)}
          end
        end, ModuleEnv, OptionTEs),

        {lists:append(EnumExports), ModuleEnv1};

      {struct, _, {con_token, _, Con}, FieldTEs} ->
        Atom = list_to_atom(Con),
        Arity = length(FieldTEs),
        Value = {{global_fn, Atom}, Arity},
        {[{Atom, Arity}], env_set(Con, Value, ModuleEnv)};

      {struct, _, {gen_te, _, {con_token, _, Con}, _}, FieldTEs} ->
        Atom = list_to_atom(Con),
        Arity = length(FieldTEs),
        Value = {{global_fn, Atom}, Arity},
        {[{Atom, Arity}], env_set(Con, Value, ModuleEnv)};

      _ -> {[], ModuleEnv}
    end
  end, Env#{'*module' => Module}, Defs).

populate_direct_imports(#comp{module=Module, deps=Deps, enums=Enums}, Env) ->
  lists:foldl(fun({DepModule, Idents}, ModuleEnv) ->
    lists:foldl(fun(Ident, NestedEnv) ->
      case Ident of
        {var, _, Name} ->
          {_, Arity} = maps:get({DepModule, Name}, NestedEnv),
          env_set(Name, {{external, DepModule}, Arity}, NestedEnv);

        {con_token, _, Name} ->
          % Name may refer to a type or a variant. We don't need to import
          % types, so only import the variant if it exists.
          case maps:find({DepModule, Name}, NestedEnv) of
            {ok, {_, Arity}} ->
              env_set(Name, {{external, DepModule}, Arity}, NestedEnv);
            error -> NestedEnv
          end;

        {variants, _, Name} ->
          Con = lists:concat([DepModule, '.', Name]),
          Variants = maps:get(Con, Enums),

          lists:foldl(fun(Variant, FoldEnv) ->
            {_, Arity} = maps:get({DepModule, Variant}, FoldEnv),
            env_set(Variant, {{external, DepModule}, Arity}, FoldEnv)
          end, NestedEnv, Variants)
      end
    end, ModuleEnv, Idents)
  end, Env#{'*module' => Module}, Deps).

compile_ast(Comp, Exports, Env) ->
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
  ModuleEnv = Env#{'*module' => Module},
  Reps = lists:flatmap(fun(Node) -> rep(Node, ModuleEnv) end, Defs),

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

rep({global, Loc, {var, _, Name}, Expr, _}, Env) ->
  Line = ?START_LINE(Loc),
  case Expr of
    {fn, _, Args, _} ->
      {'fun', _, {clauses, Clauses}} = rep(Expr, Env),
      [{function, Line, list_to_atom(Name), length(Args), Clauses}];

    _ ->
      {{global, Atom}, _} = env_get(Name, Env),
      Gm = gm(module(Env)),

      excluder_remove('_@gm_find'),
      excluder_remove('_@gm_set'),

      FindCall = {call, Line, {atom, Line, '_@gm_find'},
        [{atom, Line, Gm}, {atom, Line, Atom}]},
      SetCall = {call, Line, {atom, Line, '_@gm_set'},
        [{atom, Line, Gm}, {atom, Line, Atom}, rep(Expr, Env)]},

      Var = {var, Line, unique("_@Value")},
      Case = {'case', Line, FindCall, [
        {clause, Line, [{tuple, Line, [{atom, Line, ok}, Var]}], [], [Var]},
        {clause, Line, [{atom, Line, error}], [], [SetCall]}
      ]},
      Clause = {clause, Line, [], [], [Case]},
      [{function, Line, list_to_atom(Name), 0, [Clause]}]
  end;

rep({enum, _, _, OptionTEs}, _) ->
  FnOptionTEs = lists:filter(fun({option, _, _, ArgsTE, _}) ->
    length(ArgsTE) > 0
  end, OptionTEs),

  lists:map(fun({option, _, {con_token, Loc, Con}, ArgsTE, KeyNode}) ->
    Line = ?START_LINE(Loc),
    ArgsRep = lists:map(fun(_) ->
      Atom = unique("_@Arg"),
      {var, Line, Atom}
    end, ArgsTE),

    ConAtom = list_to_atom(Con),
    {KeyLine, Key} = case KeyNode of
      none -> {Line, ConAtom};
      {some, {atom, KeyLoc, Key_}} -> {?START_LINE(KeyLoc), Key_}
    end,

    Body = [{tuple, Line, [{atom, KeyLine, Key} | ArgsRep]}],
    Clause = {clause, Line, ArgsRep, [], Body},
    {function, Line, ConAtom, length(ArgsTE), [Clause]}
  end, FnOptionTEs);

rep({struct, Loc, StructTE, FieldTEs}, Env) ->
  {Line, Con} = case StructTE of
    {con_token, ConLoc, Con_} -> {?START_LINE(ConLoc), Con_};
    {gen_te, _, {con_token, ConLoc, Con_}, _} -> {?START_LINE(ConLoc), Con_}
  end,

  {ArgsRep, Env1} = lists:mapfoldl(fun(Sig, FoldEnv) ->
    {sig, _, {var, _, FieldName}=Var, _} = Sig,
    FoldEnv1 = bind(FieldName, unknown, FoldEnv),
    {rep(Var, FoldEnv1), FoldEnv1}
  end, Env, FieldTEs),

  Pairs = lists:map(fun({sig, _, {var, FieldLoc, FieldName}=Var, _}) ->
    {{atom, FieldLoc, list_to_atom(FieldName)}, Var}
  end, FieldTEs),
  Body = [rep({map, Loc, Pairs}, Env1)],

  Clause = {clause, Line, ArgsRep, [], Body},
  [{function, Line, list_to_atom(Con), length(FieldTEs), [Clause]}];

rep({sig, _, _, _}, _) -> [];

rep({fn, Loc, Args, Expr}, Env) ->
  Names = gb_sets:union(lists:map(fun type_system:pattern_names/1, Args)),
  Env1 = gb_sets:fold(fun(Name, FoldEnv) ->
    bind(Name, unknown, FoldEnv)
  end, Env, Names),

  Patterns = lists:map(fun(Pattern) ->
    rep(Pattern, Env1#{'*in_pattern' => true})
  end, Args),

  Line = ?START_LINE(Loc),
  Clause = {clause, Line, Patterns, [], [rep(Expr, Env1)]},
  {'fun', Line, {clauses, [Clause]}};

rep({binary_op, _, ':', Expr, _}, Env) -> rep(Expr, Env);

rep({none, Loc}, _) -> eabs(none, ?START_LINE(Loc));
rep({N, Loc, V}, _)
  when N == int; N == float; N == bool; N == str; N == atom ->
    eabs(V, ?START_LINE(Loc));
rep({char, Loc, V}, _) ->
  % special case; erl_parse:abstract will give us {integer, _, _}
  {char, ?START_LINE(Loc), V};

% only occurs in patterns
rep({'_', Loc}, _) -> {var, ?START_LINE(Loc), '_'};

rep({list, Loc, Elems}, Env) ->
  lists:foldr(fun(E, FoldRep) ->
    ERep = rep(E, Env),
    {cons, element(2, ERep), ERep, FoldRep}
  end, {nil, ?START_LINE(Loc)}, Elems);

rep({cons, _, Elems, Tail}, Env) ->
  lists:foldr(fun(E, FoldRep) ->
    ERep = rep(E, Env),
    {cons, element(2, ERep), ERep, FoldRep}
  end, rep(Tail, Env), Elems);

rep({tuple, Loc, Elems}, Env) ->
  {tuple, ?START_LINE(Loc), lists:map(fun(E) -> rep(E, Env) end, Elems)};

rep({map, Loc, Pairs}, Env) ->
  PairsRep = lists:map(fun({K, V}) ->
    KRep = rep(K, Env),
    VRep = rep(V, Env),
    {map_field_assoc, element(2, KRep), KRep, VRep}
  end, Pairs),
  {map, ?START_LINE(Loc), PairsRep};

rep({N, Loc, Name}, Env) when N == var; N == con_token; N == var_value ->
  Line = ?START_LINE(Loc),
  case env_get(Name, Env) of
    % global variable handled by the global manager
    {{global, Atom}, _} -> {call, Line, {atom, Line, Atom}, []};
    {{option, Key}, _} -> {atom, Line, Key};
    {{option, _, Atom}, Arity} -> {'fun', Line, {function, Atom, Arity}};
    {{global_fn, Atom}, Arity} -> {'fun', Line, {function, Atom, Arity}};
    {{external, Module}, _} ->
      rep({field, Loc, {con_token, Loc, Module}, {N, Loc, Name}}, Env);
    {Atom, _} when is_atom(Atom) -> {var, Line, Atom}
  end;

rep({anon_record, Loc, Inits}, Env) ->
  Pairs = lists:map(fun({init, _, {var, VarLoc, Name}, Expr}) ->
    {{atom, VarLoc, list_to_atom(Name)}, Expr}
  end, Inits),
  rep({map, Loc, Pairs}, Env);

rep({anon_record_ext, Loc, Expr, AllInits}, Env) ->
  Inits = lists:map(fun(InitOrExt) ->
    setelement(1, InitOrExt, init)
  end, AllInits),
  ExprRep = rep(Expr, Env),
  RecordRep = rep({anon_record, Loc, Inits}, Env),
  call(maps, merge, [ExprRep, RecordRep], ?START_LINE(Loc));

rep({record, Loc, _, Inits}, Env) -> rep({anon_record, Loc, Inits}, Env);

rep({record_ext, Loc, _, Expr, AllInits}, Env) ->
  rep({anon_record_ext, Loc, Expr, AllInits}, Env);

rep({field_fn, _, {var, Loc, Name}}, _) ->
  Line = ?START_LINE(Loc),
  RecordVar = {var, Line, 'Record'},
  Atom = list_to_atom(Name),
  Body = [call(maps, get, [{atom, Line, Atom}, RecordVar], Line)],
  Clause = {clause, Line, [RecordVar], [], Body},
  {'fun', Line, {clauses, [Clause]}};

% N can be var_value if we're called by rep({var_value, _, _}, _) above
rep({field, Loc, Expr, {N, _, Name}}, Env)
    when N == var; N == con_token; N == var_value ->
  Line = ?START_LINE(Loc),
  case Expr of
    {con_token, _, Module} ->
      Mod = list_to_atom(Module),
      case maps:get({Module, Name}, Env) of
        % global variable handled by the global manager
        {{global, Atom}, _} -> call(Mod, Atom, [], Line);
        {{option, Key}, _} -> {atom, Line, Key};
        {{option, _, Atom}, Arity} ->
          {'fun', Line,
            {function, eabs(Mod, Line), eabs(Atom, Line), eabs(Arity, Line)}};
        {{global_fn, Atom}, Arity} ->
          {'fun', Line,
            {function, eabs(Mod, Line), eabs(Atom, Line), eabs(Arity, Line)}}
      end;

    _ ->
      Atom = list_to_atom(Name),
      call(maps, get, [{atom, Line, Atom}, rep(Expr, Env)], Line)
  end;

rep({app, _, {con_token, Loc, Name}, Args}, #{'*in_pattern' := true}=Env) ->
  {{option, Key, _}, _} = env_get(Name, Env),
  ArgsRep = lists:map(fun(Arg) -> rep(Arg, Env) end, Args),

  Line = ?START_LINE(Loc),
  % It's possible that this is actually a partial application, but we can't
  % successfully pattern match a newly generated function anyway, so as long as
  % our pattern fails (which it will, because a function won't match a tuple),
  % we're good.
  {tuple, Line, [{atom, Line, Key} | ArgsRep]};

rep({app, _, {field, Loc, {con_token, _, Module}, {con_token, _, Name}}, Args},
    #{'*in_pattern' := true}=Env) ->
  {{option, Key, _}, _} = maps:get({Module, Name}, Env),
  ArgsRep = lists:map(fun(Arg) -> rep(Arg, Env) end, Args),

  Line = ?START_LINE(Loc),
  % It's possible that this is actually a partial application, but we can't
  % successfully pattern match a newly generated function anyway, so as long as
  % our pattern fails (which it will, because a function won't match a tuple),
  % we're good.
  {tuple, Line, [{atom, Line, Key} | ArgsRep]};

rep({app, Loc, Expr, RawArgs}, Env) ->
  ExprRep = rep(Expr, Env),
  Line = ?START_LINE(Loc),

  Arity = arity(Expr, Env),
  Args = case Arity of
    0 ->
      {none, _} = hd(RawArgs),
      tl(RawArgs);
    _ -> RawArgs
  end,
  NumArgs = length(Args),

  if
    Arity == unknown ->
      ArgsListRep = rep({list, Loc, Args}, Env),
      excluder_remove('_@curry'),
      {call, Line, {atom, Line, '_@curry'},
        [ExprRep, ArgsListRep, {integer, Line, Line}]};

    NumArgs < Arity ->
      NewArgsRep = lists:map(fun(_) ->
        {var, Line, unique("_@Arg")}
      end, lists:seq(NumArgs + 1, Arity)),

      ArgsListRep = rep({list, Loc, Args}, Env),
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
      ImmArgsRep = lists:map(fun(Arg) -> rep(Arg, Env) end, ImmArgs),

      Call = case ExprRep of
        {'fun', _, {function, Atom, _}} ->
          {call, Line, {atom, Line, Atom}, ImmArgsRep};
        _ -> {call, Line, ExprRep, ImmArgsRep}
      end,

      if
        NumArgs == Arity -> Call;
        true ->
          RestArgs = lists:sublist(Args, Arity + 1, NumArgs),
          RestArgsListRep = rep({list, Loc, RestArgs}, Env),
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

rep({'if', Loc, Cond, Then, Else}, Env) ->
  Line = ?START_LINE(Loc),
  ThenBody = case Else of
    {none, _} -> [rep(Then, Env), {atom, Line, none}];
    _ -> [rep(Then, Env)]
  end,

  % must factor out cond into its own variable, since it might not be a valid
  % guard clause; TODO: optimize by not doing this if valid guard
  CondLine = ?START_LINE(?LOC(Cond)),
  CondVar = {var, CondLine, unique("_@Cond")},
  Match = {match, CondLine, CondVar, rep(Cond, Env)},

  ElseClause = {clause, Line, [], [[{atom, Line, true}]], [rep(Else, Env)]},
  Clauses = [{clause, Line, [], [[CondVar]], ThenBody}, ElseClause],
  {block, Line, [Match, {'if', Line, Clauses}]};

rep({'let', Loc, Bindings, Then}, Env) ->
  {InitsRep, Env1} = lists:mapfoldl(fun({binding, _, Pattern, Expr}, FoldEnv) ->
    {PatternRep, ExprRep, FoldEnv1} = rep_pattern(Pattern, Expr, FoldEnv),
    {{match, element(2, PatternRep), PatternRep, ExprRep}, FoldEnv1}
  end, Env, Bindings),

  {block, ?START_LINE(Loc), InitsRep ++ [rep(Then, Env1)]};

rep({if_let, Loc, Pattern, Expr, Then, Else}, Env) ->
  Line = ?START_LINE(Loc),
  {PatternRep, ExprRep, Env1} = rep_pattern(Pattern, Expr, Env),
  ThenBody = case Else of
    {none, _} -> [rep(Then, Env1), {atom, Line, none}];
    _ -> [rep(Then, Env1)]
  end,

  CaseClauses = [
    {clause, Line, [PatternRep], [], ThenBody},
    {clause, Line, [{var, Line, '_'}], [], [rep(Else, Env)]}
  ],
  {'case', Line, ExprRep, CaseClauses};

rep({match, Loc, Expr, Cases}, Env) ->
  ExprRep = rep(Expr, Env),
  CaseClauses = lists:map(fun({'case', _, Pattern, Then}) ->
    % TODO: use arity(Expr) in case of simple pattern?
    Env1 = gb_sets:fold(fun(Name, FoldEnv) ->
      bind(Name, unknown, FoldEnv)
    end, Env, type_system:pattern_names(Pattern)),

    PatternRep = rep(Pattern, Env1#{'*in_pattern' => true}),
    Body = [rep(Then, Env1)],
    {clause, element(2, PatternRep), [PatternRep], [], Body}
  end, Cases),

  {'case', ?START_LINE(Loc), ExprRep, CaseClauses};

rep({block, Loc, Exprs}, Env) ->
  {block, ?START_LINE(Loc), lists:map(fun(E) -> rep(E, Env) end, Exprs)};

rep({binary_op, Loc, Op, Left, Right}, Env) ->
  Line = ?START_LINE(Loc),
  LeftRep = rep(Left, Env),
  RightRep = rep(Right, Env),

  case Op of
    '++' ->
      excluder_remove('_@concat'),
      {call, Line, {atom, Line, '_@concat'}, [LeftRep, RightRep]};
    '--' ->
      excluder_remove('_@separate'),
      {call, Line, {atom, Line, '_@separate'}, [LeftRep, RightRep]};
    '|>' ->
      case Right of
        {app, Expr, Args} -> rep({app, Loc, Expr, [Left | Args]}, Env);
        _ -> rep({app, Loc, Right, [Left]}, Env)
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

rep({unary_op, Loc, Op, Expr}, Env) ->
  Line = ?START_LINE(Loc),
  ExprRep = rep(Expr, Env),

  case Op of
    '!' -> {op, Line, 'not', ExprRep};
    '#' -> call(gb_sets, from_list, [ExprRep], Line);
    % $ used by the type system to treat Char as Int, but they're the same
    '$' -> ExprRep;
    '-' -> {op, Line, '-', ExprRep};
    'discard' -> {block, Line, [ExprRep, {atom, Line, none}]}
  end.

% recursive definitions allowed for simple pattern functions
rep_pattern({var, _, Name}=Pattern, {fn, _, Args, _}=Expr, Env) ->
  Env1 = bind(Name, length(Args), Env),
  PatternRep = rep(Pattern, Env1#{'*in_pattern' => true}),

  % We're unsure whether the named fun is going to be used (i.e. whether the
  % named fun is recursive), so we give it a name prefixed with an underscore
  % to prevent unused errors.
  Atom = unique([$_ | Name]),
  Env2 = env_set(Name, {Atom, length(Args)}, Env1),

  {'fun', FunLine, {clauses, Clauses}} = rep(Expr, Env2),
  NamedFun = {named_fun, FunLine, Atom, Clauses},

  % Use Env1, not Env2, as the named fun is not accessible to the outer scope.
  {PatternRep, NamedFun, Env1};

rep_pattern(Pattern, Expr, Env) ->
  % TODO arity(Expr) for simple patterns
  Env1 = gb_sets:fold(fun(Name, FoldEnv) ->
    bind(Name, unknown, FoldEnv)
  end, Env, type_system:pattern_names(Pattern)),
  {rep(Pattern, Env1#{'*in_pattern' => true}), rep(Expr, Env), Env1}.

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
module(Env) -> maps:get('*module', Env).
gm(Module) -> list_to_atom(Module ++ "_gm").

env_set(Name, Value, Env) -> Env#{{module(Env), Name} => Value}.
env_get(Name, Env) -> maps:get({module(Env), Name}, Env).

arity({fn, _, Args, _}, _) -> length(Args);
arity({binary_op, _, ':', Expr, _}, Env) -> arity(Expr, Env);
arity({N, _, Name}, Env) when N == var; N == con_token ->
  {_, Arity} = env_get(Name, Env),
  Arity;
arity({field_fn, _, _}, _) -> 1;
% TODO: we can figure this out in some cases from typing info or analysis
arity({field, _, _, _}, _) -> unknown;
% TODO: field for module access!!
arity({app, _, Expr, Args}, Env) ->
  case arity(Expr, Env) of
    unknown -> unknown;
    FnArity ->
      Arity = FnArity - length(Args),
      if
        Arity =< 0 -> unknown;
        true -> Arity
      end
  end;
arity({native, _, _, _, Arity}, _) -> Arity;
arity({N, _, _, Then, Else}, Env) when N == 'if'; N == if_let ->
  case Else of
    {none, _} -> error;
    _ -> case arity(Then, Env) of
      unknown -> arity(Else, Env);
      Arity -> Arity
    end
  end;
arity({'let', _, _, Then}, Env) -> arity(Then, Env);
arity({match, _, _, Cases}, Env) ->
  lists:foldl(fun({_, Expr}, Arity) ->
    case Arity of
      unknown -> arity(Expr, Env);
      _ -> Arity
    end
  end, unknown, Cases);
arity({block, _, Exprs}, Env) -> arity(lists:last(Exprs), Env).

call(Mod, Fn, ArgsRep, Line) ->
  {call, Line, {remote, Line, {atom, Line, Mod}, {atom, Line, Fn}}, ArgsRep}.

bind([H | T]=Name, Arity, Env) ->
  CapName = string:to_upper([H]) ++ T,
  env_set(Name, {unique(CapName), Arity}, Env).

unique(Prefix) ->
  list_to_atom(lists:concat([Prefix, '@', counter_next()])).

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
