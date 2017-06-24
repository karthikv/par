-module(code_gen).
-export([
  compile_ast/2,
  run_ast/2,
  counter_run/1,
  excluder_run/1
]).

-include("errors.hrl").
-define(COUNTER_NAME, code_gen_counter).
-define(EXCLUDER_NAME, code_gen_excluder).

compile_ast(Ast, Path) ->
  counter_spawn(),
  excluder_spawn(gb_sets:from_list(['_@curry', '_@concat', '_@separate'])),

  {module, _, {con_token, _, Mod}, Defs} = Ast,
  Gm = list_to_atom(lists:concat([Mod, '_gm'])),

  Env = lists:foldl(fun(Node, FoldEnv) ->
    case Node of
      {global, _, {var, _, Name}, {fn, _, Args, _}} ->
        FoldEnv#{Name => {{global_fn, list_to_atom(Name)}, length(Args)}};
      {global, _, {var, _, Name}, _} ->
        FoldEnv#{Name => {{global, list_to_atom(Name)}, unknown}};
      {enum_token, _, _, OptionTEs} ->
        lists:foldl(fun({{con_token, _, Con}, ArgsTE, KeyNode}, NestedEnv) ->
          Name = atom_to_list(Con),
          NumArgs = length(ArgsTE),
          Key = case KeyNode of
            default -> Con;
            {atom, _, Key_} -> Key_
          end,

          case NumArgs of
            0 -> NestedEnv#{Name => {{option, Key}, badarity}};
            _ ->
              Value = {{option, Key, Con}, NumArgs},
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
  end, #{'*gm' => Gm}, Defs),

  Reps = lists:flatmap(fun(Node) -> rep(Node, Env) end, Defs),
  Excluded = excluder_all(),

  % remove everything except necessary functions
  Utils = lists:filter(fun
    ({function, _, Atom, _, _}) -> not gb_sets:is_member(Atom, Excluded);
    (_) -> false
  end, code_gen_utils_parsed:forms()),

  LibForms = [
    {attribute, 1, file, {"[par-compiler]", 1}},
    {attribute, 1, module, Mod},
    {attribute, 1, compile, [export_all, no_auto_import]},
    {attribute, 1, on_load, {'_@on_load', 0}},
    rep_on_load_fn(Gm, Defs) |
    Utils
  ],
  CodeForms = [{attribute, 1, file, {Path, 1}} | Reps],

  {ok, Mod, Binary} = compile:forms(LibForms ++ CodeForms),
  {Mod, Binary}.

run_ast(Ast, Path) ->
  {Mod, Binary} = compile_ast(Ast, Path),
  code:purge(Mod),
  code:load_binary(Mod, "", Binary),
  Mod:main().

rep({global, Line, {var, _, Name}, Expr}, Env) ->
  case Expr of
    {fn, _, Args, _} ->
      {'fun', _, {clauses, Clauses}} = rep(Expr, Env),
      [{function, Line, list_to_atom(Name), length(Args), Clauses}];

    _ ->
      Env1 = Env#{'*populating_gm' => true},
      % TODO: don't need to create an extra fun here
      Fun = rep({fn, Line, [], Expr}, Env1),

      #{Name := {{global, Atom}, _}, '*gm' := Gm} = Env1,
      Call = {call, Line, {atom, Line, '_@gm_maybe_set'},
        [{atom, Line, Gm}, {atom, Line, Atom}, Fun]},
      Clause = {clause, Line, [], [], [Call]},
      [{function, Line, list_to_atom(Name), 0, [Clause]}]
  end;

rep({enum_token, _, _, OptionTEs}, _) ->
  FnOptionTEs = lists:filter(fun({_, ArgsTE, _}) ->
    length(ArgsTE) > 0
  end, OptionTEs),

  lists:map(fun({{con_token, Line, Con}, ArgsTE, KeyNode}) ->
    ArgsRep = lists:map(fun(_) ->
      Atom = unique("_@Arg"),
      {var, Line, Atom}
    end, ArgsTE),

    {KeyLine, Key} = case KeyNode of
      default -> {Line, Con};
      {atom, KeyLine_, Key_} -> {KeyLine_, Key_}
    end,

    Body = [{tuple, Line, [{atom, KeyLine, Key} | ArgsRep]}],
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

rep({cons, _, Elems, Tail}, Env) ->
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
    % global variable handled by the global manager
    {{global, Atom}, _} ->
      #{'*gm' := Gm} = Env,
      case maps:find('*populating_gm', Env) of
        {ok, true} -> {call, Line, {atom, Line, Atom}, []};
        _ ->
          {call, Line, {atom, Line, '_@gm_get'},
            [{atom, Line, Gm}, {atom, Line, Atom}]}
      end;

    {{option, Key}, _} -> {atom, Line, Key};
    {{option, _, Atom}, Arity} -> {'fun', Line, {function, Atom, Arity}};
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
  #{Name := {{option, Key, _}, _}} = Env,
  ArgsRep = lists:map(fun(Arg) -> rep(Arg, Env) end, Args),
  % It's possible that this is actually a partial application, but we can't
  % successfully pattern match a newly generated function anyway, so as long as
  % our pattern fails (which it will, because a function won't match a tuple),
  % we're good.
  {tuple, Line, [{atom, Line, Key} | ArgsRep]};

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
      excluder_remove('_@curry'),
      {call, Line, {atom, Line, '_@curry'},
        [ExprRep, ArgsListRep, {integer, Line, Line}]};

    NumArgs < Arity ->
      NewArgsRep = lists:map(fun(_) ->
        {var, Line, unique("_@Arg")}
      end, lists:seq(NumArgs + 1, Arity)),

      ArgsListRep = rep({list, Line, Args}, Env),
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
          RestArgsListRep = rep({list, Line, RestArgs}, Env),
          excluder_remove('_@curry'),
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

  % must factor out cond into its own variable, since it might not be a valid
  % guard clause; TODO: optimize by not doing this if valid guard
  CondLine = element(2, Cond),
  CondVar = {var, CondLine, unique("_@Cond")},
  Match = {match, CondLine, CondVar, rep(Cond, Env)},

  ElseClause = {clause, Line, [], [[{atom, Line, true}]], [rep(Else, Env)]},
  Clauses = [{clause, Line, [], [[CondVar]], ThenBody}, ElseClause],
  {block, Line, [Match, {'if', Line, Clauses}]};

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
    end, Env, type_system:pattern_names(Pattern)),

    PatternRep = rep(Pattern, Env1#{'*in_pattern' => true}),
    Body = [rep(Then, Env1)],
    {clause, element(2, PatternRep), [PatternRep], [], Body}
  end, Cases),

  {'case', Line, ExprRep, CaseClauses};

rep({block, Line, Exprs}, Env) ->
  {block, Line, lists:map(fun(E) -> rep(E, Env) end, Exprs)};

rep({Op, Line, Left, Right}, Env) ->
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
  end, Env, type_system:pattern_names(Pattern)),
  {rep(Pattern, Env1#{'*in_pattern' => true}), rep(Expr, Env), Env1}.

rep_on_load_fn(Gm, Ast) ->
  StartGm = {call, 1, {atom, 1, '_@gm_spawn'}, [{atom, 1, Gm}]},

  GlobalVarNames = lists:filtermap(fun
    ({global, _, _, {fn, _, _, _}}) -> false;
    ({global, _, {var, _, Name}, _}) -> {true, Name};
    (_) -> false
  end, Ast),

  Calls = lists:map(fun(Name) ->
    {call, 1, {atom, 1, list_to_atom(Name)}, []}
  end, GlobalVarNames),

  % must return ok for module load to succeed
  Clause = {clause, 1, [], [], [StartGm | Calls] ++ [{atom, 1, ok}]},
  {function, 1, '_@on_load', 0, [Clause]}.

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
  Env#{Name => {unique(CapName), Arity}}.

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
