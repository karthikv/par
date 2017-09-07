-module(utils).
-export([
  resolve_con/2,
  qualify/2,
  unqualify/1,
  impl_key/1,
  ivs/1,
  ivs/2,
  arg_ts/1,
  absolute/1,
  pretty_csts/1,
  pretty/1
]).
-include("common.hrl").

resolve_con(RawCon, C) ->
  Con = utils:qualify(RawCon, C),
  case maps:find(Con, C#ctx.aliases) of
    {ok, {_, {con, NewCon}, false}} -> NewCon;
    {ok, {_, {gen, NewCon, _}, false}} -> NewCon;
    _ -> Con
  end.

qualify(RawCon, C) ->
  case maps:is_key(RawCon, C#ctx.types) of
    % existing type or iface
    true -> RawCon;
    false ->
      case string:chr(RawCon, $.) of
        0 -> lists:concat([C#ctx.module, '.', RawCon]);
        _ -> RawCon
      end
  end.

unqualify(Con) ->
  case string:chr(Con, $.) of
    0 -> Con;
    Index -> lists:sublist(Con, Index + 1, length(Con))
  end.

impl_key({lam, _, _}) -> "Function";
impl_key({lam, _, _, _}) -> "Function";
impl_key({tuple, _}) -> "Tuple";
impl_key({con, Con}) -> Con;
impl_key({gen, Con, _}) -> Con;
impl_key({record, _, _}) -> "Record";
impl_key({record_ext, _, _, _}) -> "Record";
impl_key(unit) -> "()".

ivs(T) -> ivs(T, gb_sets:new()).

ivs(T, InitSeenVs) ->
  {IVs, _} = lists:foldl(fun({_, V}=IV, {IVs, SeenVs}) ->
    case gb_sets:is_member(V, SeenVs) of
      true -> {IVs, SeenVs};
      false -> {[IV | IVs], gb_sets:add(V, SeenVs)}
    end
  end, {[], InitSeenVs}, ivs_list(T)),
  IVs.

ivs_list({lam, ArgT, ReturnT}) -> ivs_list(ArgT) ++ ivs_list(ReturnT);
ivs_list({lam, _, ArgT, ReturnT}) -> ivs_list({lam, ArgT, ReturnT});
ivs_list({tuple, ElemTs}) -> lists:flatmap(fun ivs_list/1, ElemTs);
ivs_list({tv, _, none, _}) -> [];
ivs_list({tv, V, AllIs, _}) ->
  Is = gb_sets:delete_any("Num", AllIs),
  case gb_sets:is_empty(Is) of
    true -> [];
    false -> [{Is, V}]
  end;
ivs_list({con, _}) -> [];
ivs_list({gen, Gen, ParamTs}) ->
  GenIVs = case Gen of
    {tv, _, _, _} -> ivs_list(Gen);
    _ -> []
  end,
  GenIVs ++ lists:flatmap(fun ivs_list/1, ParamTs);
% ivs_list({inst, ...}) ommitted; they should be resolved
ivs_list({record, _, FieldMap}) ->
  SortedKeys = lists:sort(maps:keys(FieldMap)),
  lists:flatmap(fun(Key) ->
    ivs_list(maps:get(Key, FieldMap))
  end, SortedKeys);
ivs_list({record_ext, _, BaseT, Ext}) ->
  ivs_list(BaseT) ++ ivs_list({record, none, Ext});
ivs_list(unit) -> [].

arg_ts({lam, ArgT, ReturnT}) -> [ArgT | arg_ts(ReturnT)];
arg_ts(_) -> [].

absolute(Path) ->
  FullPath = filename:absname(Path),
  absolute(filename:split(FullPath), []).

absolute([], Accum) -> filename:join(lists:reverse(Accum));
absolute([H | T], Accum) ->
  case H of
    "." -> absolute(T, Accum);
    ".." -> absolute(T, tl(Accum));
    _ -> absolute(T, [H | Accum])
  end.

pretty_csts([]) -> [];
pretty_csts([{T1, T2, Module, Loc, From} | Rest]) ->
  [{pretty(T1), pretty(T2), Module, Loc, From} | pretty_csts(Rest)].

pretty({lam, ArgT, ReturnT}) ->
  Format = case ArgT of
    {lam, _, _} -> "(~s) -> ~s";
    {lam, _, _, _} -> "(~s) -> ~s";
    _ -> "~s -> ~s"
  end,
  ?FMT(Format, [pretty(ArgT), pretty(ReturnT)]);
pretty({lam, _, ArgT, ReturnT}) -> pretty({lam, ArgT, ReturnT});
pretty({tuple, ElemTs}) ->
  PrettyElemTs = lists:map(fun(T) -> pretty(T) end, ElemTs),
  ?FMT("(~s)", [string:join(PrettyElemTs, ", ")]);
pretty({tv, RawV, Is, Rigid}) ->
  % all generated Vs are prefixed with *, but user-inputted ones in signatures
  % lack the leading *
  V = case RawV of
    [$* | T] -> T;
    _ -> RawV
  end,
  Str = if
    Is == none -> V;
    true ->
      % TODO: keep qualified when ambiguous
      Unqualified = lists:map(fun(I) ->
        utils:unqualify(I)
      end, gb_sets:to_list(Is)),
      ?FMT("~s ~~ ~s", [V, string:join(Unqualified, " ~ ")])
  end,

  case Rigid of
    false -> Str;
    true -> ?FMT("rigid(~s)", [Str])
  end;
pretty({set_iface, I}) -> ?FMT("I = ~s", [utils:unqualify(I)]);
% TODO: keep qualified when ambiguous
pretty({con, Con}) -> utils:unqualify(Con);
pretty({gen, "List", [ElemT]}) -> ?FMT("[~s]", [pretty(ElemT)]);
pretty({gen, Con, ParamTs}) ->
  PrettyParamTs = lists:map(fun(T) -> pretty(T) end, ParamTs),
  ?FMT("~s<~s>", [utils:unqualify(Con), string:join(PrettyParamTs, ", ")]);
pretty({inst, TV}) -> ?FMT("inst(~s)", [pretty(TV)]);
pretty({record, _, FieldMap}) -> ?FMT("{ ~s }", [pretty_field_map(FieldMap)]);
pretty({record_ext, _, BaseT, Ext}) ->
  ?FMT("{ ~s | ~s }", [pretty(BaseT), pretty_field_map(Ext)]);
pretty(unit) -> "()".

pretty_field_map(FieldMap) ->
  FieldStrs = maps:fold(fun(Name, T, Strs) ->
    [?FMT("~s : ~s", [Name, pretty(T)]) | Strs]
  end, [], FieldMap),
  string:join(lists:sort(FieldStrs), ", ").
