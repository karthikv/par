-module(par_native).
-export([
  init/1,
  gm_find/2,
  gm_set/3,
  concat/2,
  separate/2,
  to_str/1
]).

init(Mod) ->
  gm_spawn(),
  Mod:'_@init'(ordsets:new()).

gm_spawn() ->
  case whereis(par_gm) of
    undefined ->
      Pid = spawn(fun() -> gm_run(#{}) end),
      register(par_gm, Pid);

    Pid ->
      Pid ! {self(), reset},
      receive
        reset_ok -> true
      after
        1000 -> error("couldn't reset globals")
      end
  end.

gm_run(Globals) ->
  receive
    {Pid, reset} ->
      Pid ! reset_ok,
      gm_run(#{});
    {Pid, get, Key} ->
      Pid ! {get_ok, maps:get(Key, Globals)},
      gm_run(Globals);
    {Pid, find, Key} ->
      Pid ! {find_ok, maps:find(Key, Globals)},
      gm_run(Globals);
    {Pid, set, Key, Value} ->
      Pid ! set_ok,
      gm_run(Globals#{Key => Value})
  end.

gm_find(Mod, Atom) ->
  Key = {Mod, Atom},
  par_gm ! {self(), find, Key},
  receive
    {find_ok, Result} -> Result
  after
    1000 -> error({"couldn't find global", Key})
  end.

gm_set(Mod, Atom, Value) ->
  Key = {Mod, Atom},
  par_gm ! {self(), set, Key, Value},
  receive
    set_ok -> Value
  after
    1000 -> error({"couldn't set global", Key, Value})
  end.

concat(Left, Right) ->
  if
    is_binary(Left) -> <<Left/binary, Right/binary>>;
    is_list(Left) -> Left ++ Right;
    is_map(Left) -> maps:merge(Left, Right)
  end.

separate(Left, Right) ->
  if
    is_list(Left) ->
      Map = maps:from_list([{Elem, true} || Elem <- Right]),
      lists:filter(fun(Elem) ->
        not maps:is_key(Elem, Map)
      end, Left);
    is_map(Left) -> maps:without(maps:keys(Right), Left)
  end.

to_str(Str) when is_binary(Str) -> Str;
to_str(Term) -> iolist_to_binary(to_iolist(Term)).

to_iolist(Int) when is_integer(Int) -> integer_to_binary(Int);
% Can't use float_to_binary() for float, since it shows too much precision,
% so fallback to the last clause.
% Atom also accounts for booleans. Note that we don't fallback for atoms
% specifically because formatting a capitalized atom includes single quotes.
to_iolist(Atom) when is_atom(Atom) -> atom_to_binary(Atom, utf8);
to_iolist(Str) when is_binary(Str) -> [$", Str, $"];
to_iolist(Tuple) when is_atom(element(1, Tuple)) ->
  [Atom | Rest] = tuple_to_list(Tuple),
  [to_iolist(Atom), $(, comma_sep(lists:map(fun to_iolist/1, Rest)), $)];
to_iolist(Tuple) when is_tuple(Tuple) ->
  [$(, comma_sep(lists:map(fun to_iolist/1, tuple_to_list(Tuple))), $)];
to_iolist(List) when is_list(List) ->
  [$[, comma_sep(lists:map(fun to_iolist/1, List)), $]];
to_iolist(#{'_@type' := 'Set'}=Map) ->
  Elems = maps:keys(maps:remove('_@type', Map)),
  [$#, $[, comma_sep(lists:map(fun to_iolist/1, Elems)), $]];
to_iolist(#{'_@type' := Type}=Map) ->
  FieldMap = maps:remove('_@type', Map),
  case maps:size(FieldMap) of
    0 -> <<"{}">>;
    _ ->
      Fields = lists:map(fun({K, V}) ->
        [to_iolist(K), <<" = ">>, to_iolist(V)]
      end, maps:to_list(maps:remove('_@type', Map))),
      Prefix = case Type of
        '_@Record' -> [];
        _ -> [to_iolist(Type), $\s]
      end,
      [Prefix, ${, $\s, comma_sep(Fields), $\s, $}]
  end;
to_iolist(Map) when map_size(Map) == 0 -> <<"{}">>;
to_iolist(Map) when is_map(Map) ->
  Pairs = lists:map(fun({K, V}) ->
    [to_iolist(K), <<" => ">>, to_iolist(V)]
  end, maps:to_list(Map)),
  [${, $\s, comma_sep(Pairs), $\s, $}];
to_iolist(Term) -> io_lib:format("~p", [Term]).

comma_sep([]) -> [];
comma_sep([H]) -> [H];
comma_sep([H | T]) -> [H, $,, $\s | comma_sep(T)].
