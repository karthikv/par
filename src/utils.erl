-module(utils).
-export([
  resolve_con/2,
  qualify/2,
  unqualify/1,
  impl_key/1,
  ivs/1,
  ivs/2,
  builtin_is/0,
  all_ivs/1,
  arg_ts/1,
  family_is/2,
  absolute/1,
  pretty_csts/1,
  pretty/1
]).
-include("common.hrl").

resolve_con(RawCon, C) ->
  Con = utils:qualify(RawCon, C),
  case maps:find(Con, C#ctx.aliases) of
    {ok, {_, {con, NewCon}, false}} -> NewCon;
    {ok, {_, {gen, {con, NewCon}, _}, false}} -> NewCon;
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

% The keys function, tuple, and record are in lowercase so they don't conflict
% with the name of a Con.
impl_key({lam, _, _}) -> "function";
impl_key({lam, _, _, _, _}) -> "function";
impl_key({tuple, Elems}) -> lists:concat([length(Elems), "-element tuple"]);
impl_key({con, Con}) -> Con;
impl_key({gen, {con, Con}, _}) -> Con;
impl_key({record, _, _}) -> "record";
impl_key({record_ext, _, _, _}) -> "record";
impl_key(unit) -> "()".

ivs(T) -> ivs(T, gb_sets:new()).

ivs(T, InitSeenVs) ->
  {IVs, _} = lists:foldl(fun({AllIs, V}, {IVs, SeenVs}) ->
    Is = gb_sets:difference(AllIs, builtin_is()),
    Seen = gb_sets:is_member(V, SeenVs),
    Empty = gb_sets:is_empty(Is),

    if
      not Seen and not Empty -> {[{Is, V} | IVs], gb_sets:add(V, SeenVs)};
      true -> {IVs, SeenVs}
    end
  end, {[], InitSeenVs}, ivs_list(T)),
  IVs.

builtin_is() -> gb_sets:from_list(["Num", "Ord", "Concatable", "Separable"]).

all_ivs(T) ->
  {IVs, _} = lists:foldl(fun({_, V}=IV, {IVs, SeenVs}) ->
    case gb_sets:is_member(V, SeenVs) of
      true -> {IVs, SeenVs};
      _ -> {[IV | IVs], gb_sets:add(V, SeenVs)}
    end
  end, {[], gb_sets:new()}, ivs_list(T)),
  IVs.

ivs_list({lam, ArgT, ReturnT}) -> ivs_list(ArgT) ++ ivs_list(ReturnT);
ivs_list({lam, _, _, ArgT, ReturnT}) -> ivs_list({lam, ArgT, ReturnT});
ivs_list({tuple, ElemTs}) -> lists:flatmap(fun ivs_list/1, ElemTs);
ivs_list({tv, _, none, _}) -> [];
ivs_list({tv, V, Is, _}) -> [{Is, V}];
ivs_list({con, _}) -> [];
ivs_list({gen, _, ParamTs}) -> lists:flatmap(fun ivs_list/1, ParamTs);
ivs_list({gen, V, Is, BaseT, ParamTs}) ->
  BaseIVs = case Is of
    none -> ivs_list(BaseT);
    _ -> [{Is, V} | ivs_list(BaseT)]
  end,
  BaseIVs ++ ivs_list({gen, {con, ""}, ParamTs});
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

family_is(I, _) when I == "Ord"; I == "Concatable"; I == "Separable" ->
  gb_sets:singleton(I);
family_is("Num", _) -> gb_sets:from_list(["Num", "Ord"]);
family_is(I, Ifaces) ->
  {_, _, Parents} = maps:get(I, Ifaces),
  gb_sets:fold(fun(ParentI, Family) ->
    gb_sets:union(Family, family_is(ParentI, Ifaces))
  end, gb_sets:add(I, Parents), Parents).

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
    {lam, _, _, _, _} -> "(~s) -> ~s";
    _ -> "~s -> ~s"
  end,
  ?FMT(Format, [pretty(ArgT), pretty(ReturnT)]);
pretty({lam, _, _, ArgT, ReturnT}) -> pretty({lam, ArgT, ReturnT});
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
pretty({set_ifaces, Is}) ->
  Unqualified = lists:map(fun(I) ->
    utils:unqualify(I)
  end, gb_sets:to_list(Is)),
  ?FMT("set ifaces ~s", [string:join(Unqualified, " ~ ")]);
% TODO: keep qualified when ambiguous
pretty({con, Con}) -> utils:unqualify(Con);
pretty({gen, {con, "List"}, [ElemT]}) -> ?FMT("[~s]", [pretty(ElemT)]);
pretty({gen, ConT, ParamTs}) ->
  PrettyParamTs = lists:map(fun(T) -> pretty(T) end, ParamTs),
  ?FMT("~s<~s>", [pretty(ConT), string:join(PrettyParamTs, ", ")]);
pretty({gen, _, Is, BaseT, ParamTs}) ->
  PrettyParamTs = lists:map(fun(T) -> pretty(T) end, ParamTs),
  {PrettyBaseT, AllIs} = case BaseT of
    {tv, V, BaseIs, Rigid} ->
      MergedIs = if
        Is == none -> BaseIs;
        BaseIs == none -> Is;
        true -> gb_sets:union(Is, BaseIs)
      end,
      {pretty({tv, V, none, Rigid}), MergedIs};

    _ -> {pretty(BaseT), Is}
  end,

  PrettyIs = case AllIs of
    none -> "";
    _ ->
      Unqualified = lists:map(fun(I) ->
        utils:unqualify(I)
      end, gb_sets:to_list(AllIs)),
      ?FMT(" ~~ ~s", [string:join(Unqualified, " ~ ")])
  end,
  ?FMT("~s<~s>~s", [PrettyBaseT, string:join(PrettyParamTs, ", "), PrettyIs]);
pretty({inst, _, TV}) -> ?FMT("inst(~s)", [pretty(TV)]);
pretty({inst, _, GVs, T}) ->
  ?FMT("inst(~s, ~s)", [gb_sets:to_list(GVs), pretty(T)]);
pretty({record, _, FieldMap}) -> ?FMT("{ ~s }", [pretty_field_map(FieldMap)]);
pretty({record_ext, _, BaseT, Ext}) ->
  ?FMT("{ ~s | ~s }", [pretty(BaseT), pretty_field_map(Ext)]);
pretty(unit) -> "()".

pretty_field_map(FieldMap) ->
  FieldStrs = maps:fold(fun(Name, T, Strs) ->
    [?FMT("~s : ~s", [Name, pretty(T)]) | Strs]
  end, [], FieldMap),
  string:join(lists:sort(FieldStrs), ", ").
