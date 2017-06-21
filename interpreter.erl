-module(interpreter).
-export([reload/1, run_file/2, run_prg/2, run_ast/2, env_run/2]).

-define(ENV_NAME, interpreter_env).

reload(Syntax) ->
  par:reload(Syntax),

  code:purge(?MODULE),
  {ok, _} = compile:file(?MODULE),
  code:load_file(?MODULE).

run_file(Name, Args) ->
  {ok, Prg} = file:read_file(Name),
  run_prg(binary_to_list(Prg), Args).

run_prg(Prg, Args) ->
  case par:infer_prg(Prg) of
    {errors, Errs} -> par:report_errors(Errs);
    {ok, _, Ast} -> run_ast(Ast, Args)
  end.

run_ast(Ast, Args) ->
  ID = env_spawn(),
  lists:foreach(fun(Node) -> init(Node, ID) end, Ast),

  lists:foreach(fun(Node) ->
    case Node of
      % strictly evaluate all globals
      {global, _, Var, _} -> eval(Var, ID);
      _ -> true
    end
  end, Ast),

  apply(eval({var, 0, "main"}, ID), Args).

init({global, _, {var, _, Name}, Expr}, ID) ->
  env_set(Name, {lazy, Expr}, ID);

init({enum_token, _, _, OptionTEs}, ID) ->
  lists:foreach(fun({{con_token, _, Con}, ArgsTE, KeyNode}) ->
    Key = case KeyNode of
      default -> Con;
      {atom, _, Key_} -> Key_
    end,

    V = if
      length(ArgsTE) == 0 -> Key;
      true ->
        make_fun(length(ArgsTE), fun(Vs) ->
          list_to_tuple([Key | Vs])
        end)
    end,

    env_set(atom_to_list(Con), {option, Key, V}, ID)
  end, OptionTEs);

init({struct_token, _, StructTE, {record_te, _, FieldTEs}}, ID) ->
  Con = case StructTE of
    {con_token, _, Con_} -> Con_;
    {gen_te, _, {con_token, _, Con_}, _} -> Con_
  end,

  FieldAtoms = lists:map(fun({{var, _, FieldName}, _}) ->
    list_to_atom(FieldName)
  end, FieldTEs),
  StructV = make_fun(length(FieldTEs), fun(Vs) ->
    maps:from_list(lists:zip(FieldAtoms, Vs))
  end),

  env_set(atom_to_list(Con), StructV, ID);

init({sig, _, _, _}, _) -> true.

eval({fn, _, Args, Expr}, ID) ->
  make_fun(length(Args), fun(Vs) ->
    NewID = if
      length(Args) == 0 -> ID;
      true ->
        ChildID = env_child(ID),
        lists:foreach(fun({{var, _, Name}, V}) ->
          env_set(Name, V, ChildID)
        end, lists:zip(Args, Vs)),
        ChildID
    end,

    eval(Expr, NewID)
  end);

eval({'::', _, Expr, _}, ID) -> eval(Expr, ID);

eval({none, _}, _) -> none;
eval({N, _, V}, _)
  when N == int; N == float; N == bool; N == char; N == str; N == atom -> V;

eval({list, _, Elems}, ID) ->
  lists:map(fun(E) -> eval(E, ID) end, Elems);

eval({cons, Line, Elems, List}, ID) ->
  ToPrepend = eval({list, Line, Elems}, ID),
  lists:foldr(fun(V, FoldList) ->
    [V | FoldList]
  end, eval(List, ID), ToPrepend);

eval({tuple, Line, Elems}, ID) ->
  list_to_tuple(eval({list, Line, Elems}, ID));

eval({map, _, Pairs}, ID) ->
  List = lists:map(fun({K, V}) ->
    {eval(K, ID), eval(V, ID)}
  end, Pairs),
  maps:from_list(List);

eval({var, _, Name}, ID) ->
  case env_get(Name, ID) of
    {lazy, Expr} ->
      V = eval(Expr, ID),
      env_update(Name, V, ID),
      V;
    {option, _, V} -> V;
    V -> V
  end;

eval({con_var, Line, Name}, ID) -> eval({var, Line, Name}, ID);

eval({record, _, Inits}, ID) ->
  Pairs = lists:map(fun({{var, _, Name}, Expr}) ->
    {list_to_atom(Name), eval(Expr, ID)}
  end, Inits),
  maps:from_list(Pairs);

eval({update_record, Line, Expr, Inits}, C) ->
  Record = eval(Expr, C),
  maps:merge(Record, eval({record, Line, Inits}, C));

eval({record, Line, _, Inits}, ID) -> eval({record, Line, Inits}, ID);

eval({field, _, {var, _, Name}}, _) ->
  Atom = list_to_atom(Name),
  fun(Record) -> maps:get(Atom, Record) end;

eval({field, Line, Expr, Var}, ID) ->
  Record = eval(Expr, ID),
  Fun = eval({field, Line, Var}, ID),
  Fun(Record);

eval({app, _, Expr, Args}, ID) ->
  Fun = eval(Expr, ID),
  Vs = case length(Args) of
    0 -> [none];
    _ -> lists:map(fun(Arg) -> eval(Arg, ID) end, Args)
  end,
  code_gen_utils:'_@curry'(Fun, Vs, ?LINE);

eval({native, _, {atom, _, Module}, {var, _, Name}, Arity}, _) ->
  Fn = list_to_atom(Name),
  fun Module:Fn/Arity;

eval({'if', _, Expr, Then, Else}, ID) ->
  V = case eval(Expr, ID) of
    true -> eval(Then, ID);
    false -> eval(Else, ID)
  end,
  case Else of
    {none, _} -> none;
    _ -> V
  end;

eval({'let', _, Inits, Then}, ID) ->
  ChildID = lists:foldl(fun({Pattern, Expr}, FoldID) ->
    case eval_pattern(Pattern, Expr, FoldID) of
      {{false, V}, _} -> error({badmatch, V, Pattern});
      {true, FoldChildID} -> FoldChildID
    end
  end, ID, Inits),

  eval(Then, ChildID);

eval({if_let, _, {Pattern, Expr}, Then, Else}, ID) ->
  V = case eval_pattern(Pattern, Expr, ID) of
    {{false, _}, _} -> eval(Else, ID);
    {true, ChildID} -> eval(Then, ChildID)
  end,

  case Else of
    {none, _} -> none;
    _ -> V
  end;

eval({'match', _, Expr, Cases}, ID) ->
  V = eval(Expr, ID),
  match_cases(V, Cases, ID);

eval({block, _, Exprs}, ID) ->
  lists:foldl(fun(Expr, _) -> eval(Expr, ID) end, none, Exprs);

eval({Op, _, Left, Right}, ID) ->
  LeftV = eval(Left, ID),
  RightV = eval(Right, ID),

  case Op of
    '==' -> LeftV == RightV;
    '!=' -> LeftV /= RightV;
    '||' -> LeftV or RightV;
    '&&' -> LeftV and RightV;
    '|>' -> code_gen_utils:'_@curry'(RightV, [LeftV], ?LINE);
    '>' -> LeftV > RightV;
    '<' -> LeftV < RightV;
    '>=' -> LeftV >= RightV;
    '<=' -> LeftV =< RightV;
    '+' -> LeftV + RightV;
    '-' -> LeftV - RightV;
    '*' -> LeftV * RightV;
    '/' -> LeftV / RightV;
    '%' -> LeftV rem RightV;
    '++' ->
      if
        is_binary(LeftV) -> <<LeftV/binary, RightV/binary>>;
        is_list(LeftV) -> LeftV ++ RightV;
        is_map(LeftV) -> maps:merge(LeftV, RightV);
        true ->
          true = gb_sets:is_set(LeftV),
          gb_sets:union(LeftV, RightV)
      end;
    '--' ->
      if
        is_list(LeftV) ->
          Set = gb_sets:from_list(RightV),
          lists:filter(fun(Elem) ->
            not gb_sets:is_member(Elem, Set)
          end, LeftV);
        true ->
          true = gb_sets:is_set(LeftV),
          gb_sets:subtract(LeftV, RightV)
      end
  end;

eval({Op, _, Expr}, ID) ->
  V = eval(Expr, ID),

  case Op of
    '!' -> not V;
    '#' -> gb_sets:from_list(V);
    % $ used by the type system to treat Char as Int, but they're the same
    '$' -> V;
    '-' -> -V;
    'discard' -> none
  end.

eval_pattern({var, _, Name}, {fn, _, _, _}=Expr, ID) ->
  ChildID = env_child(ID),
  env_set(Name, eval(Expr, ChildID), ChildID),
  {true, ChildID};

eval_pattern(Pattern, Expr, ID) ->
  V = eval(Expr, ID),
  ChildID = env_child(ID),
  lists:foreach(fun(Name) ->
    env_set(Name, {}, ChildID)
  end, gb_sets:to_list(par:pattern_names(Pattern))),

  case match(V, Pattern, ChildID) of
    false -> {{false, V}, ChildID};
    true -> {true, ChildID}
  end.

make_fun(Arity, Callback) ->
  ArgsRep = lists:map(fun(Num) ->
    {var, ?LINE, list_to_atom(lists:concat(['_@', Num]))}
  end, lists:seq(1, Arity)),
  ArgsListRep = lists:foldr(fun(FoldArgRep, FoldListRep) ->
    {cons, ?LINE, FoldArgRep, FoldListRep}
  end, {nil, ?LINE}, ArgsRep),

  CallbackVar = {var, ?LINE, '_@Callback'},
  Body = [{call, ?LINE, CallbackVar, [ArgsListRep]}],
  Clause = {clause, ?LINE, ArgsRep, [], Body},
  Expr = {'fun', ?LINE, {clauses, [Clause]}},

  Bindings = erl_eval:add_binding(
    element(3, CallbackVar),
    Callback,
    erl_eval:new_bindings()
  ),

  {value, Value, _} = erl_eval:expr(Expr, Bindings),
  Value.

match_cases(V, [], _) -> error({badmatch, V});
match_cases(V, [{Pattern, Expr} | Rest], ID) ->
  ChildID = env_child(ID),
  lists:foreach(fun(Name) ->
    env_set(Name, {}, ChildID)
  end, gb_sets:to_list(par:pattern_names(Pattern))),

  case match(V, Pattern, ChildID) of
    true -> eval(Expr, ChildID);
    false -> match_cases(V, Rest, ID)
  end.

match(V1, {N, _, V2}, _) when N == int; N == float; N == bool; N == char;
    N == str; N == atom ->
  V1 == V2;

match(V1, {var, _, Name}, ID) ->
  case env_get(Name, ID) of
    {} ->
      env_update(Name, V1, ID),
      true;
    V2 -> V1 == V2
  end;

match(V1, {var_value, Line, Name}, ID) -> V1 == eval({var, Line, Name}, ID);
match(_, {'_', _}, _) -> true;

match(V1, {con_var, _, Name}, ID) ->
  case env_get(Name, ID) of
    {option, _, V2} -> V1 == V2;
    V2 -> V1 == V2
  end;

match(V, {app, _, {con_var, Line, Name}, Args}, ID) ->
  {option, Key, _} = env_get(Name, ID),
  if
    length(Args) == 0 -> V == Key;
    true ->
      match(tuple_to_list(V), {list, Line, [{atom, Line, Key} | Args]}, ID)
  end;

match(V, {list, _, List}, ID) ->
  if
    length(V) /= length(List) -> false;
    true ->
      lists:foldl(fun({ExpV, Elem}, Matched) ->
        case Matched of
          false -> false;
          true -> match(ExpV, Elem, ID)
        end
      end, true, lists:zip(V, List))
  end;

match(V, {cons, Line, List, Rest}, ID) ->
  if
    length(V) < length(List) -> false;
    true ->
      SubV = lists:sublist(V, length(List)),
      RestV = lists:sublist(V, length(List) + 1, length(V)),

      case match(SubV, {list, Line, List}, ID) of
        false -> false;
        true -> match(RestV, Rest, ID)
      end
  end;

match(V, {tuple, _, Elems}, ID) ->
  if
    tuple_size(V) /= length(Elems) -> false;
    true ->
      {_, Matched} = lists:foldl(fun(Elem, {Index, Matched}) ->
        NewMatched = case Matched of
          false -> false;
          true -> match(element(Index, V), Elem, ID)
        end,
        {Index + 1, NewMatched}
      end, {1, true}, Elems),
      Matched
  end.

env_spawn() ->
  case whereis(?ENV_NAME) of
    undefined ->
      Pid = spawn_link(?MODULE, env_run, [2, #{1 => {#{}, undefined}}]),
      register(?ENV_NAME, Pid),
      1;

    Pid ->
      Pid ! {self(), reset},
      receive
        reset_ok -> 1;
        Unexpected ->
          error({"unexpected reset response", Unexpected})
      after 1000 ->
        error("couldn't reset env")
      end
  end.

env_run(NextID, Env) ->
  receive
    {Pid, reset} ->
      Pid ! reset_ok,
      env_run(2, #{1 => {#{}, undefined}});
    {Pid, child, ParentID} ->
      Pid ! {child_ok, NextID},
      env_run(NextID + 1, Env#{NextID => {#{}, ParentID}});
    {Pid, find, Name, ID} ->
      #{ID := {Bindings, ParentID}} = Env,
      Pid ! {find_ok, maps:find(Name, Bindings), ParentID},
      env_run(NextID, Env);
    {Pid, set, Name, V, ID} ->
      #{ID := {Bindings, ParentID}} = Env,
      Pid ! set_ok,
      env_run(NextID, Env#{ID := {Bindings#{Name => V}, ParentID}});
    Unexpected ->
      io:format("unexpected env message ~p~n", [Unexpected]),
      env_run(NextID, Env)
  end.

env_child(ParentID) ->
  ?ENV_NAME ! {self(), child, ParentID},
  receive
    {child_ok, NextID} -> NextID;
    Unexpected ->
      error({"unexpected child response", Unexpected})
  after 1000 ->
    error({"couldn't make child env", ParentID})
  end.

env_get(Name, ID) ->
  ?ENV_NAME ! {self(), find, Name, ID},
  receive
    {find_ok, {ok, V}, _} -> V;
    {find_ok, error, undefined} -> error({badkey, Name});
    {find_ok, error, ParentID} -> env_get(Name, ParentID);
    Unexpected ->
      error({"unexpected find response", Name, ID, Unexpected})
  after 1000 ->
    error({"couldn't get env", Name, ID})
  end.

env_set(Name, V, ID) ->
  ?ENV_NAME ! {self(), set, Name, V, ID},
  receive
    set_ok -> ok;
    Unexpected ->
      error({"unexpected set response", Name, V, ID, Unexpected})
  after 1000 ->
    error({"couldn't set env", Name, V, ID})
  end.

env_update(Name, V, ID) ->
  ?ENV_NAME ! {self(), find, Name, ID},
  receive
    {find_ok, {ok, _}, _} -> env_set(Name, V, ID);
    {find_ok, error, undefined} -> error({badkey, Name});
    {find_ok, error, ParentID} -> env_update(Name, V, ParentID);
    Unexpected ->
      error({"unexpected find response", Name, V, ID, Unexpected})
  after 1000 ->
    error({"couldn't update env", Name, V, ID})
  end.
