-module(interpreter).
-export([run_ast/2, env_run/2]).

-include("common.hrl").
-define(ENV_NAME, interpreter_env).

run_ast(Ast, Args) ->
  ID = env_spawn(),
  {module, _, _, _, Defs} = Ast,

  lists:foreach(fun(Node) -> init(Node, ID) end, Defs),
  lists:foreach(fun(Node) ->
    case Node of
      % strictly evaluate all globals
      {global, _, Var, _, _} -> eval(Var, ID);
      _ -> true
    end
  end, Defs),

  apply(eval({var, 0, "main"}, ID), Args).

init({global, _, {var, _, Name}, Expr, _}, ID) ->
  env_set(Name, {lazy, Expr}, ID);

init({enum, _, _, OptionTEs}, ID) ->
  lists:foreach(fun({option, _, {con_token, _, Con}, ArgsTE, KeyNode}) ->
    Key = case KeyNode of
      'None' -> list_to_atom(Con);
      {'Some', {atom, _, Key_}} -> Key_
    end,

    V = if
      length(ArgsTE) == 0 -> Key;
      true ->
        make_fun(length(ArgsTE), fun(Vs) ->
          list_to_tuple([Key | Vs])
        end)
    end,

    env_set(Con, {option, Key, V}, ID)
  end, OptionTEs);

init({struct, _, StructTE, FieldTEs}, ID) ->
  Con = case StructTE of
    {con_token, _, Con_} -> Con_;
    {gen_te, _, {con_token, _, Con_}, _} -> Con_
  end,

  FieldAtoms = lists:map(fun({sig, _, {var, _, FieldName}, _}) ->
    list_to_atom(FieldName)
  end, FieldTEs),
  StructV = make_fun(length(FieldTEs), fun(Vs) ->
    maps:from_list(lists:zip(FieldAtoms, Vs))
  end),

  env_set(Con, {value, StructV}, ID);

init({sig, _, _, _}, _) -> true.

eval({fn, _, _, Args, Expr}, ID) ->
  make_fun(length(Args), fun(Vs) ->
    NewID = if
      length(Args) == 0 -> ID;
      true ->
        ChildID = env_child(ID),
        Names = ordsets:union(lists:map(fun type_system:pattern_names/1, Args)),

        lists:foreach(fun(Name) ->
          env_set(Name, unset, ChildID)
        end, ordsets:to_list(Names)),

        lists:foreach(fun({V, Pattern}) ->
          case match(V, Pattern, ChildID) of
            false -> error(function_clause);
            true -> true
          end
        end, lists:zip(Vs, Args)),

        ChildID
    end,

    eval(Expr, NewID)
  end);

eval({expr_sig, _, _, Expr, _}, ID) -> eval(Expr, ID);

eval({unit, _}, _) -> {};
eval({N, _, V}, _)
  when N == int; N == float; N == bool; N == char; N == str; N == atom -> V;

eval({list, _, Elems}, ID) ->
  lists:map(fun(E) -> eval(E, ID) end, Elems);

eval({cons, Loc, Elems, List}, ID) ->
  ToPrepend = eval({list, Loc, Elems}, ID),
  lists:foldr(fun(V, FoldList) ->
    [V | FoldList]
  end, eval(List, ID), ToPrepend);

eval({tuple, Loc, Elems}, ID) ->
  list_to_tuple(eval({list, Loc, Elems}, ID));

eval({map, _, Assocs}, ID) ->
  List = lists:map(fun({assoc, _, Key, Value}) ->
    {eval(Key, ID), eval(Value, ID)}
  end, Assocs),
  maps:from_list(List);

eval({N, _, Name}, ID) when N == var; N == con_token ->
  case env_get(Name, ID) of
    {lazy, Expr} ->
      V = eval(Expr, ID),
      env_update(Name, {value, V}, ID),
      V;
    {option, _, V} -> V;
    {value, V} -> V
  end;

eval({var_ref, Loc, _, Name}, ID) -> eval({var, Loc, Name}, ID);

eval({anon_record, _, _, Inits}, ID) ->
  Pairs = lists:map(fun({init, _, {var, _, Name}, Expr}) ->
    V = case Expr of
      {fn, _, _, _, _} ->
        ChildID = env_child(ID),
        ExprV = eval(Expr, ChildID),
        env_set(Name, {value, ExprV}, ChildID),
        ExprV;

      _ -> eval(Expr, ID)
    end,

    {list_to_atom(Name), V}
  end, Inits),

  maps:from_list(Pairs);

eval({anon_record_ext, Loc, Ref, Expr, AllInits}, C) ->
  Record = eval(Expr, C),
  Inits = lists:map(fun(InitOrExt) ->
    setelement(1, InitOrExt, init)
  end, AllInits),
  maps:merge(Record, eval({anon_record, Loc, Ref, Inits}, C));

eval({record, Loc, _, Inits}, ID) -> eval({anon_record, Loc, none, Inits}, ID);

eval({record_ext, Loc, _, Expr, AllInits}, ID) ->
  eval({anon_record_ext, Loc, none, Expr, AllInits}, ID);

eval({field_fn, _, {var, _, Name}}, _) ->
  Atom = list_to_atom(Name),
  fun(Record) -> maps:get(Atom, Record) end;

eval({field, Loc, Expr, Var}, ID) ->
  Record = eval(Expr, ID),
  Fun = eval({field_fn, Loc, Var}, ID),
  Fun(Record);

eval({app, _, Expr, Args}, ID) ->
  Fun = eval(Expr, ID),
  Vs = case length(Args) of
    0 -> [{}];
    _ -> lists:map(fun(Arg) -> eval(Arg, ID) end, Args)
  end,
  par_native:curry(Fun, Vs, ?LINE);

eval({native, _, {atom, _, Module}, {var, _, Name}, Arity}, _) ->
  Fn = list_to_atom(Name),
  fun Module:Fn/Arity;

eval({'if', _, Expr, Then, Else}, ID) ->
  V = case eval(Expr, ID) of
    true -> eval(Then, ID);
    false -> eval(Else, ID)
  end,

  case Else of
    {unit, _} -> {};
    _ -> V
  end;

eval({'let', _, Bindings, Then}, ID) ->
  ChildID = lists:foldl(fun({binding, _, Pattern, Expr}, FoldID) ->
    case eval_pattern(Pattern, Expr, FoldID) of
      {{false, V}, _} -> error({badmatch, V, Pattern});
      {true, FoldChildID} -> FoldChildID
    end
  end, ID, Bindings),

  eval(Then, ChildID);

eval({if_let, _, Pattern, Expr, Then, Else}, ID) ->
  V = case eval_pattern(Pattern, Expr, ID) of
    {{false, _}, _} -> eval(Else, ID);
    {true, ChildID} -> eval(Then, ChildID)
  end,

  case Else of
    {unit, _} -> {};
    _ -> V
  end;

eval({'match', _, Expr, Cases}, ID) ->
  V = eval(Expr, ID),
  match_cases(V, Cases, ID);

eval({block, _, Exprs}, ID) ->
  lists:foldl(fun(Expr, _) -> eval(Expr, ID) end, {}, Exprs);

eval({binary_op, _, Op, Left, Right}, ID) ->
  LeftV = eval(Left, ID),
  % can't eval right because of short-circuiting

  case Op of
    '||' -> LeftV orelse eval(Right, ID);
    '&&' -> LeftV andalso eval(Right, ID);

    _ ->
      RightV = eval(Right, ID),

      case Op of
        '==' -> LeftV == RightV;
        '!=' -> LeftV /= RightV;
        '|>' -> par_native:curry(RightV, [LeftV], ?LINE);
        '>' -> LeftV > RightV;
        '<' -> LeftV < RightV;
        '>=' -> LeftV >= RightV;
        '<=' -> LeftV =< RightV;
        '+' -> LeftV + RightV;
        '-' -> LeftV - RightV;
        '*' -> LeftV * RightV;
        '/' -> LeftV / RightV;
        '%' -> LeftV rem RightV;
        '++' -> par_native:concat(LeftV, RightV);
        '--' -> par_native:separate(LeftV, RightV)
      end
  end;

eval({unary_op, _, Op, Expr}, ID) ->
  V = eval(Expr, ID),

  case Op of
    '!' -> not V;
    '#' ->
      Pairs = lists:map(fun(E) -> {E, true} end, V),
      maps:from_list([{'_@type', 'Set'} | Pairs]);
    % $ is used to convert Char to Int, but the underlying rep is the same
    '$' -> V;
    '-' -> -V;
    'discard' -> {};
    % assume is used to subvert the type system; it doesn't modify value
    'assume' -> V
  end.

eval_pattern({var, _, Name}, {fn, _, _, _, _}=Expr, ID) ->
  ChildID = env_child(ID),
  env_set(Name, {value, eval(Expr, ChildID)}, ChildID),
  {true, ChildID};

eval_pattern(Pattern, Expr, ID) ->
  V = eval(Expr, ID),
  ChildID = env_child(ID),
  lists:foreach(fun(Name) ->
    env_set(Name, unset, ChildID)
  end, ordsets:to_list(type_system:pattern_names(Pattern))),

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
match_cases(V, [{'case', _, Pattern, Expr} | Rest], ID) ->
  ChildID = env_child(ID),
  lists:foreach(fun(Name) ->
    env_set(Name, unset, ChildID)
  end, ordsets:to_list(type_system:pattern_names(Pattern))),

  case match(V, Pattern, ChildID) of
    true -> eval(Expr, ChildID);
    false -> match_cases(V, Rest, ID)
  end.

match(V, {unit, _}, _) -> V == {};
match(V1, {N, _, V2}, _) when N == int; N == float; N == bool; N == char;
    N == str; N == atom ->
  V1 == V2;

match(V1, {var, _, Name}, ID) ->
  case env_get(Name, ID) of
    unset ->
      env_update(Name, {value, V1}, ID),
      true;
    {value, V2} -> V1 == V2
  end;

match(V1, {var_value, Loc, Name}, ID) -> V1 == eval({var, Loc, Name}, ID);
match(_, {'_', _}, _) -> true;

match(V, {variant, _, {con_token, Loc, Name}, Args}, ID) ->
  {option, Key, _} = env_get(Name, ID),
  if
    length(Args) == 0 -> V == Key;
    true ->
      Elems = [{atom, Loc, Key} | Args],
      match(tuple_to_list(V), {list, Loc, Elems}, ID)
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

match(V, {cons, Loc, List, Rest}, ID) ->
  if
    length(V) < length(List) -> false;
    true ->
      SubV = lists:sublist(V, length(List)),
      RestV = lists:sublist(V, length(List) + 1, length(V)),

      case match(SubV, {list, Loc, List}, ID) of
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
