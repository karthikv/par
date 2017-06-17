-module(code_gen).
-export([reload/1, run_ast/2]).

reload(Syntax) ->
  par:reload(Syntax),

  code:soft_purge(code_gen_utils),
  {ok, _} = compile:file(code_gen_utils),
  code:load_file(code_gen_utils),

  code:purge(?MODULE),
  {ok, _} = compile:file(?MODULE),
  code:load_file(?MODULE).

run_ast(Ast, Mod) ->
  Env = lists:foldl(fun(Node, FoldEnv) ->
    case Node of
      {global, _, {var, _, Name}, {fn, _, Args, _}} ->
        FoldEnv#{Name => {{global_fn, list_to_atom(Name)}, length(Args)}};
      {global, _, {var, _, Name}, _} ->
        Value = {{ets, list_to_atom(lists:concat([Mod, '|', Name]))}, badarity},
        FoldEnv#{Name => Value};
      {enum_token, _, _, OptionTEs} ->
        lists:foldl(fun({{con_token, Line, Con}, ArgsTE, KeyNode}, NestedEnv) ->
          Name = atom_to_list(Con),
          NumArgs = length(ArgsTE),
          LitNode = case KeyNode of
            default -> {atom, Line, Con};
            {atom, _, _} -> KeyNode
          end,

          case NumArgs of
            0 -> NestedEnv#{Name => {{lit, LitNode}, badarity}};
            _ ->
              Value = {{global_fn, Con}, NumArgs},
              NestedEnv#{Name => Value}
          end
        end, FoldEnv, OptionTEs);
      {struct_token, _, {con_token, _, Con}, {record_te, _, FieldTEs}} ->
        FoldEnv#{atom_to_list(Con) => {{global_fn, Con}, length(FieldTEs)}};
      {struct_token, _, {gen_te, _, {con_token, _, Con}, _},
          {record_te, _, FieldTEs}} ->
        FoldEnv#{atom_to_list(Con) => {{global_fn, Con}, length(FieldTEs)}};
      _ -> FoldEnv
    end
  end, #{}, Ast),

  {ok, Parsed} = epp:parse_file('code_gen_utils.erl', []),
  % remove attributes and eof
  Utils = lists:sublist(Parsed, 4, length(Parsed) - 4),

  Reps = lists:flatmap(fun(Node) -> rep(Node, Env) end, Ast),
  Forms = [
    {attribute, 1, module, Mod},
    {attribute, 1, export, [{init, 0}, {import, 1}]},
    rep_init_fn(Env),
    rep_import_fn(Env) |
    Utils ++ Reps
  ],

  {ok, Mod, Binary} = compile:forms(Forms),
  ok = file:write_file(lists:concat([Mod, '.beam']), Binary),

  code:purge(Mod),
  code:load_file(Mod),
  Mod:init(),
  (Mod:import(main))().

rep({global, Line, {var, _, Name}, Expr}, Env) ->
  case Expr of
    {fn, _, Args, _} ->
      {'fun', _, {clauses, Clauses}} = rep(Expr, Env),
      [{function, Line, list_to_atom(Name), length(Args), Clauses}];

    _ ->
      Env1 = Env#{'*call_constant_fns' => true},
      % TODO: don't need to create an extra fun here
      Fun = rep({fn, Line, [], Expr}, Env1),

      #{Name := {{ets, Atom}, _}} = Env1,
      Call = {call, Line, {atom, Line, '_@ets_lookup_or_insert'},
        [{atom, Line, Atom}, Fun]},
      Clause = {clause, Line, [], [], [Call]},
      [{function, Line, list_to_atom(Name), 0, [Clause]}]
  end;

rep({enum_token, _, _, OptionTEs}, _) ->
  FnOptionTEs = lists:filter(fun({_, ArgsTE, _}) ->
    length(ArgsTE) > 0
  end, OptionTEs),

  lists:map(fun({{con_token, Line, Con}, ArgsTE, KeyNode}) ->
    ArgsRep = lists:map(fun(Num) ->
      Atom = list_to_atom(lists:concat(['_@', Num])),
      {var, Line, Atom}
    end, lists:seq(1, length(ArgsTE))),

    {AtomLine, Atom} = case KeyNode of
      default -> {Line, Con};
      {atom, AtomLine_, Atom_} -> {AtomLine_, Atom_}
    end,

    Body = [{tuple, Line, [{atom, AtomLine, Atom} | ArgsRep]}],
    Clause = {clause, Line, ArgsRep, [], Body},
    {function, Line, Con, length(ArgsTE), [Clause]}
  end, FnOptionTEs);

rep({struct_token, _, StructTE, {record_te, _, FieldTEs}}, Env) ->
  {Line, Con} = case StructTE of
    {con_token, Line_, Con_} -> {Line_, Con_};
    {gen_te, _, {con_token, Line_, Con_}, _} -> {Line_, Con_}
  end,

  {ArgsRep, Env1} = lists:mapfoldl(fun({{var, _, FieldName}=Var, _}, FoldEnv) ->
    FoldEnv1 = bind(FieldName, unknown, FoldEnv),
    {rep(Var, FoldEnv1), FoldEnv1}
  end, Env, FieldTEs),

  Pairs = lists:map(fun({{var, FieldLine, FieldName}=Var, _}) ->
    {{atom, FieldLine, list_to_atom(FieldName)}, Var}
  end, FieldTEs),
  Body = [rep({map, Line, Pairs}, Env1)],

  Clause = {clause, Line, ArgsRep, [], Body},
  [{function, Line, Con, length(FieldTEs), [Clause]}];

rep({sig, _, _, _}, _) -> [];

rep({fn, Line, Args, Expr}, Env) ->
  {Patterns, Env1} = lists:mapfoldl(fun({var, _, Name}=Var, FoldEnv) ->
    FoldEnv1 = bind(Name, unknown, FoldEnv),
    {rep(Var, FoldEnv1), FoldEnv1}
  end, Env, Args),
  Clause = {clause, Line, Patterns, [], [rep(Expr, Env1)]},
  {'fun', Line, {clauses, [Clause]}};

rep({'::', _, Expr, _}, Env) -> rep(Expr, Env);

rep({none, Line}, _) -> erl_parse:abstract(none, Line);
rep({N, Line, V}, _)
  when N == int; N == float; N == bool; N == str; N == atom ->
    erl_parse:abstract(V, Line);
rep({char, Line, V}, _) ->
  % special case; erl_parse:abstract will give us {integer, _, _}
  {char, Line, V};

% only occurs in patterns
rep({'_', Line}, _) -> {var, Line, '_'};

rep({list, Line, Elems}, Env) ->
  lists:foldr(fun(E, FoldRep) ->
    ERep = rep(E, Env),
    {cons, element(2, ERep), ERep, FoldRep}
  end, {nil, Line}, Elems);

% only occurs in patterns
rep({list, _, Elems, Tail}, Env) ->
  lists:foldr(fun(E, FoldRep) ->
    ERep = rep(E, Env),
    {cons, element(2, ERep), ERep, FoldRep}
  end, rep(Tail, Env), Elems);

rep({tuple, Line, Elems}, Env) ->
  {tuple, Line, lists:map(fun(E) -> rep(E, Env) end, Elems)};

rep({map, Line, Pairs}, Env) ->
  PairsRep = lists:map(fun({K, V}) ->
    KRep = rep(K, Env),
    VRep = rep(V, Env),
    {map_field_assoc, element(2, KRep), KRep, VRep}
  end, Pairs),
  {map, Line, PairsRep};

rep({N, Line, Name}, Env) when N == var; N == con_var; N == var_value ->
  case maps:get(Name, Env) of
    % global constant in ETS
    {{ets, Atom}, _} ->
      case maps:find('*call_constant_fns', Env) of
        {ok, true} -> {call, Line, {atom, Line, list_to_atom(Name)}, []};
        _ ->
          {call, Line,
            {remote, Line, {atom, Line, ets}, {atom, Line, lookup_element}},
            [{atom, Line, constants}, {atom, Line, Atom},
             {integer, Line, 2}]}
      end;

    {{lit, LitNode}, _} -> LitNode;
    {{global_fn, Atom}, Arity} -> {'fun', Line, {function, Atom, Arity}};
    {Atom, _} -> {var, Line, Atom}
  end;

rep({record, Line, Inits}, Env) ->
  Pairs = lists:map(fun({{var, VarLine, Name}, Expr}) ->
    {{atom, VarLine, list_to_atom(Name)}, Expr}
  end, Inits),
  rep({map, Line, Pairs}, Env);

rep({update_record, Line, Expr, Inits}, Env) ->
  call(maps, merge, [rep(Expr, Env), rep({record, Line, Inits}, Env)], Line);

rep({record, Line, _, Inits}, Env) -> rep({record, Line, Inits}, Env);

rep({field, _, {var, Line, Name}}, _) ->
  RecordVar = {var, Line, 'Record'},
  Atom = list_to_atom(Name),
  Body = [call(maps, get, [{atom, Line, Atom}, RecordVar], Line)],
  Clause = {clause, Line, [RecordVar], [], Body},
  {'fun', Line, {clauses, [Clause]}};

rep({field, _, Expr, {var, Line, Name}}, Env) ->
  Atom = list_to_atom(Name),
  call(maps, get, [{atom, Line, Atom}, rep(Expr, Env)], Line);

rep({app, _, {con_var, Line, Name}, Args}, #{'*in_pattern' := true}=Env) ->
  ArgsRep = lists:map(fun(Arg) -> rep(Arg, Env) end, Args),
  % It's possible that this is actually a partial application, but we can't
  % successfully pattern match a newly generated function anyway, so as long as
  % our pattern fails (which it will, because a function won't match a tuple),
  % we're good.
  {tuple, Line, [{atom, Line, list_to_atom(Name)} | ArgsRep]};

rep({app, _, Expr, RawArgs}, Env) ->
  ExprRep = rep(Expr, Env),
  Line = element(2, ExprRep),

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
      ArgsListRep = rep({list, Line, Args}, Env),
      {call, Line, {atom, Line, '_@curry'},
        [ExprRep, ArgsListRep, {integer, Line, Line}]};

    NumArgs < Arity ->
      NewArgsRep = lists:map(fun(Num) ->
        {var, Line, list_to_atom(lists:concat(['_@', Num]))}
      end, lists:seq(NumArgs + 1, Arity)),

      ArgsListRep = rep({list, Line, Args}, Env),
      NewArgsListRep = lists:foldr(fun(ArgRep, ListRep) ->
        {cons, Line, ArgRep, ListRep}
      end, {nil, Line}, NewArgsRep),

      Body = [{call, Line, {atom, Line, apply},
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
          RestArgsListRep = rep({list, Line, RestArgs}, Env),
          {call, Line, {atom, Line, '_@curry'},
            [Call, RestArgsListRep, {integer, Line, Line}]}
      end
  end;

rep({native, _, {atom, Line, Mod}, {var, _, Name}, Arity}, _) ->
  Atom = list_to_atom(Name),
  {'fun', Line,
    {function, {atom, Line, Mod}, {atom, Line, Atom}, {integer, Line, Arity}}};

rep({'if', Line, Cond, Then, Else}, Env) ->
  ThenBody = case Else of
    {none, _} -> [rep(Then, Env), {atom, Line, none}];
    _ -> [rep(Then, Env)]
  end,

  ElseClause = {clause, Line, [], [[{atom, Line, true}]], [rep(Else, Env)]},
  Clauses = [{clause, Line, [], [[rep(Cond, Env)]], ThenBody}, ElseClause],
  {'if', Line, Clauses};

rep({'let', Line, Inits, Then}, Env) ->
  {InitsRep, Env1} = lists:mapfoldl(fun({Pattern, Expr}, FoldEnv) ->
    {PatternRep, ExprRep, FoldEnv1} = rep_pattern(Pattern, Expr, FoldEnv),
    {{match, element(2, PatternRep), PatternRep, ExprRep}, FoldEnv1}
  end, Env, Inits),

  {block, Line, InitsRep ++ [rep(Then, Env1)]};

rep({if_let, Line, {Pattern, Expr}, Then, Else}, Env) ->
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

rep({'match', Line, Expr, Cases}, Env) ->
  ExprRep = rep(Expr, Env),
  CaseClauses = lists:map(fun({Pattern, Then}) ->
    % TODO: use arity(Expr) in case of simple pattern?
    Env1 = gb_sets:fold(fun(Name, FoldEnv) ->
      bind(Name, unknown, FoldEnv)
    end, Env, par:pattern_names(Pattern)),

    PatternRep = rep(Pattern, Env1#{'*in_pattern' => true}),
    Body = [rep(Then, Env1)],
    {clause, element(2, PatternRep), [PatternRep], [], Body}
  end, Cases),

  {'case', Line, ExprRep, CaseClauses};

rep({block, Line, Exprs}, Env) ->
  {block, Line, lists:map(fun(E) -> rep(E, Env) end, Exprs)};

rep({cons, Line, Elem, List}, Env) ->
  {cons, Line, rep(Elem, Env), rep(List, Env)};

rep({Op, Line, Left, Right}, Env) ->
  LeftRep = rep(Left, Env),
  RightRep = rep(Right, Env),

  case Op of
    '++' ->
      {call, Line, {atom, Line, '_@concat'}, [LeftRep, RightRep]};
    '--' ->
      {call, Line, {atom, Line, '_@separate'}, [LeftRep, RightRep]};
    '|>' ->
      case Right of
        {app, Expr, Args} -> rep({app, Line, Expr, [Left | Args]}, Env);
        _ -> rep({app, Line, Right, [Left]}, Env)
      end;
    _ ->
      Atom = case Op of
        '==' -> '==';
        '!=' -> '/=';
        '||' -> 'or';
        '&&' -> 'and';
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

rep({Op, Line, Expr}, Env) ->
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
  {var, _, Atom}=PatternRep = rep(Pattern, Env1#{'*in_pattern' => true}),

  {'fun', FunLine, {clauses, Clauses}} = rep(Expr, Env1),
  NamedFun = {named_fun, FunLine, Atom, Clauses},
  {PatternRep, NamedFun, Env1};

rep_pattern(Pattern, Expr, Env) ->
  % TODO arity(Expr) for simple patterns
  Env1 = gb_sets:fold(fun(Name, NestedEnv) ->
    bind(Name, unknown, NestedEnv)
  end, Env, par:pattern_names(Pattern)),
  {rep(Pattern, Env1#{'*in_pattern' => true}), rep(Expr, Env), Env1}.

rep_init_fn(Env) ->
  CreateTableCall = {call, 1, {atom, 1, '_@ets_create_table'},
    [{atom, 1, constants}]},

  {ResetCalls, PopulateCalls} = maps:fold(fun(Name, Value, Memo) ->
    {Reset, Populate} = Memo,
    case Value of
      {{ets, Atom}, _} ->
        ResetArgsRep = [{atom, 1, constants}, {atom, 1, Atom}],
        NewReset = [call(ets, delete, ResetArgsRep, 1) | Reset],
        NewPopulate = [{call, 1, {atom, 1, list_to_atom(Name)}, []} | Populate],
        {NewReset, NewPopulate};
      _ -> {Reset, Populate}
    end
  end, {[], []}, Env),

  Body = [CreateTableCall] ++ ResetCalls ++ PopulateCalls,
  Clause = {clause, 1, [], [], Body},
  {function, 1, 'init', 0, [Clause]}.

rep_import_fn(Env) ->
  ImportVar = {var, 1, 'Import'},
  CaseClauses = maps:fold(fun(Name, _, Clauses) ->
    VarRep = rep({var, 1, Name}, Env),
    [{clause, 1, [{atom, 1, list_to_atom(Name)}], [], [VarRep]} | Clauses]
  end, [], Env),
  Case = {'case', 1, ImportVar, CaseClauses},

  FnClause = {clause, 1, [ImportVar], [], [Case]},
  {function, 1, 'import', 1, [FnClause]}.

arity({fn, _, Args, _}, _) -> length(Args);
arity({'::', _, Expr, _}, Env) -> arity(Expr, Env);
arity({N, _, Name}, Env) when N == var; N == con_var ->
  #{Name := {_, Arity}} = Env,
  Arity;
arity({field, _, _}, _) -> 1;
% TODO: we can figure this out in some cases from typing info or analysis
arity({field, _, _, _}, _) -> unknown;
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
arity({'match', _, _, Cases}, Env) ->
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
  Atom = case maps:find(Name, Env) of
    error -> list_to_atom(CapName);
    {ok, {{ets, _}, _}} -> list_to_atom(lists:concat([CapName, '@', 1]));
    {ok, {A, _}} ->
      Num = case string:substr(atom_to_list(A), length(CapName) + 1) of
        [] -> 1;
        [$@ | NumStr] -> list_to_integer(NumStr) + 1
      end,
      list_to_atom(lists:concat([CapName, '@', Num]))
  end,

  Env#{Name => {Atom, Arity}}.
