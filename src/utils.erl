-module(utils).
-export([
  stdlib_dir/0,
  stdlib_modules/0,
  resolve_con/2,
  qualify/2,
  unqualify/1,
  unalias/2,
  subs/2,
  impl_key/1,
  ivs/1,
  ivs/2,
  builtin_is/0,
  all_ivs/1,
  tvs_list/1,
  args_ivs/1,
  args_ivs/2,
  family_is/2,
  test_names/2,
  exported_idents/3,
  prep_compiled/2,
  remove_compiled/2,
  absolute/1,
  pretty_csts/1,
  pretty/1,
  temp_dir/0,
  hex_encode/1,
  remove_mod/1
]).
-include("common.hrl").

stdlib_dir() -> utils:absolute(filename:join(code:lib_dir(par, src), "lib")).

stdlib_modules() ->
  Dir = stdlib_dir(),
  #{
    "Base" => filename:join(Dir, "base.par"),
    "List" => filename:join(Dir, "list.par"),
    "Set" => filename:join(Dir, "set.par"),
    "Map" => filename:join(Dir, "map.par"),
    "String" => filename:join(Dir, "string.par"),
    "Char" => filename:join(Dir, "char.par"),
    "File" => filename:join(Dir, "file.par"),
    "Path" => filename:join(Dir, "path.par"),
    "Test" => filename:join(Dir, "test.par")
  }.

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

unalias(T, Aliases) ->
  subs(T, #sub_opts{subs=#{}, aliases=Aliases, unalias=true}).

subs({lam, ArgTs, ReturnT}, Opts) ->
  {lam, [subs(ArgT, Opts) || ArgT <- ArgTs], subs(ReturnT, Opts)};
subs({lam, LEnv, Provided, ReturnT}, Opts) ->
  SubbedProvided = [{Type, Loc, subs(T, Opts)} || {Type, Loc, T} <- Provided],
  {lam, LEnv, SubbedProvided, subs(ReturnT, Opts)};
subs({tuple, ElemTs}, Opts) ->
  {tuple, [subs(T, Opts) || T <- ElemTs]};
subs({tv, V, Is, Rigid}=TV, #sub_opts{subs=Subs, shallow=Shallow}=Opts) ->
  case maps:find(V, Subs) of
    error -> TV;
    {ok, {rigid, V1}} -> {tv, V1, Is, true};
    {ok, {set_ifaces, NewIs}} -> {tv, V, NewIs, Rigid};
    {ok, {set_ifaces_rigid, NewIs}} -> {tv, V, NewIs, true};

    {ok, Value} ->
      Sub = if
        % Instantiation, so rigid resets to false
        is_list(Value) -> {tv, Value, Is, false};
        % Replacing with a new type entirely
        true -> Value
      end,
      if
        Shallow -> Sub;
        true -> subs(Sub, Opts)
      end
  end;
subs({con, Con}, #sub_opts{aliases=Aliases, unalias=true}=Opts) ->
  case maps:find(Con, Aliases) of
    {ok, {[], T, _}} ->
      % Don't recursively unalias, as this can cause an infinite loop with
      % recursive struct types.
      subs(T, Opts#sub_opts{unalias=false});
    error -> {con, Con}
  end;
subs({con, Con}, _) -> {con, Con};
subs({gen, {con, Con}, ParamTs}, Opts) ->
  #sub_opts{aliases=Aliases, unalias=Unalias} = Opts,
  Alias = maps:find(Con, Aliases),

  if
    not Unalias; Alias == error ->
      {gen, {con, Con}, [subs(T, Opts) || T <- ParamTs]};

    true ->
      {ok, {Vs, T, _}} = Alias,
      AliasSubs = maps:from_list(lists:zip(Vs, ParamTs)),

      % Don't recursively unalias, as this can cause an infinite loop with
      % recursive struct types.
      UnaliasedT = subs(T, #sub_opts{subs=AliasSubs}),
      subs(UnaliasedT, Opts#sub_opts{unalias=false})
  end;
subs({gen, V, Is, BaseT, ParamTs}, #sub_opts{for_err=ForErr}=Opts) ->
  case subs({tv, V, Is, false}, Opts) of
    {tv, NewV, NewIs, _} ->
      % When reporting errors, do *not* sub BaseT; if BaseT is subbed and
      % V isn't subbed, that indicates a unification error with a regular gen.
      % We avoid subbing BaseT for better error messages; instead of
      % mismatched List<A> ~ Num and [A], we get T<A> ~ Num and [A].
      SubbedBaseT = if
        ForErr -> BaseT;
        true -> subs(BaseT, Opts)
      end,
      {gen, _, SubbedParamTs} = subs({gen, {con, ""}, ParamTs}, Opts),
      {gen, NewV, NewIs, SubbedBaseT, SubbedParamTs};

    SubbedT -> SubbedT
  end;
subs({record, A, FieldMap}, #sub_opts{subs=Subs}=Opts) ->
  case maps:find(A, Subs) of
    error -> {record, A, maps:map(fun(_, T) -> subs(T, Opts) end, FieldMap)};
    {ok, {anchor, NewA}} -> subs({record, NewA, FieldMap}, Opts);
    {ok, T} -> subs(T, Opts)
  end;
subs({record_ext, A, Ext, BaseT}, #sub_opts{subs=Subs, aliases=Aliases}=Opts) ->
  case maps:find(A, Subs) of
    error ->
      NewExt = maps:map(fun(_, T) -> subs(T, Opts) end, Ext),
      consolidate({record_ext, A, NewExt, subs(BaseT, Opts)}, Aliases);
    {ok, {anchor, NewA}} ->
      subs({record_ext, NewA, Ext, BaseT}, Opts);
    {ok, T} -> subs(T, Opts)
  end;
subs({hole, Report}, _) -> {hole, Report}.

consolidate({record_ext, A, Ext2, {record_ext, _, Ext1, BaseT}}, Aliases) ->
  consolidate({record_ext, A, maps:merge(Ext1, Ext2), BaseT}, Aliases);
consolidate({record_ext, A, Ext, {record, _, FieldMap}}, _) ->
  {record, A, maps:merge(FieldMap, Ext)};
consolidate({record_ext, A, Ext, BaseT}, Aliases) ->
  case unalias(BaseT, Aliases) of
    BaseT -> {record_ext, A, Ext, BaseT};
    NewBaseT -> consolidate({record_ext, A, Ext, NewBaseT}, Aliases)
  end.

% The keys function, tuple, and record are in lowercase so they don't conflict
% with the name of a Con.
impl_key({lam, _, _}) -> "function";
impl_key({lam, _, _, _}) -> "function";
impl_key({tuple, Elems}) -> lists:concat([length(Elems), "-element tuple"]);
impl_key({con, Con}) -> Con;
impl_key({gen, {con, Con}, _}) -> Con;
impl_key({record, _, _}) -> "record";
impl_key({record_ext, _, _, _}) -> "record".

ivs(T) -> ivs(T, ordsets:new()).

ivs(T, InitSeenVs) ->
  {IVs, _} = lists:foldl(fun({AllIs, V}, {IVs, SeenVs}) ->
    Is = ordsets:subtract(AllIs, builtin_is()),
    Seen = ordsets:is_element(V, SeenVs),
    Empty = ordsets:size(Is) == 0,

    if
      not Seen and not Empty -> {[{Is, V} | IVs], ordsets:add_element(V, SeenVs)};
      true -> {IVs, SeenVs}
    end
  end, {[], InitSeenVs}, ivs_list(T)),
  IVs.

builtin_is() -> ordsets:from_list(["Num", "Ord"]).

all_ivs(T) ->
  {IVs, _} = lists:foldl(fun({_, V}=IV, {IVs, SeenVs}) ->
    case ordsets:is_element(V, SeenVs) of
      true -> {IVs, SeenVs};
      _ -> {[IV | IVs], ordsets:add_element(V, SeenVs)}
    end
  end, {[], ordsets:new()}, ivs_list(T)),
  IVs.

ivs_list(T) ->
  lists:filtermap(fun
    ({tv, V, Is, _}) when Is /= none -> {true, {Is, V}};
    ({gen, V, Is, _, _}) when Is /= none -> {true, {Is, V}};
    (_) -> false
  end, tvs_list(T)).

tvs_list(T) -> tvs_list(T, []).

% The order in which we recurse is important, as we want the TVs to be listed
% from left-to-right.
tvs_list({lam, ArgTs, ReturnT}, L) ->
  lists:foldr(fun tvs_list/2, tvs_list(ReturnT, L), ArgTs);
tvs_list({lam, _, Provided, ReturnT}, L) ->
  lists:foldr(fun({_, _, T}, FoldL) ->
    tvs_list(T, FoldL)
  end, tvs_list(ReturnT, L), Provided);
tvs_list({tuple, ElemTs}, L) -> lists:foldr(fun tvs_list/2, L, ElemTs);
tvs_list({tv, _, _, _}=TV, L) -> [TV | L];
tvs_list({con, _}, L) -> L;
tvs_list({gen, _, ParamTs}, L) -> lists:foldr(fun tvs_list/2, L, ParamTs);
tvs_list({gen, _, _, BaseT, ParamTs}=GenTV, L) ->
  % GenTVs are also included, as they're needed to compute ivs and fvs.
  [GenTV | tvs_list(BaseT, tvs_list({gen, {con, ""}, ParamTs}, L))];
% tvs_list({inst, ...}) ommitted; they should be resolved
tvs_list({record, _, FieldMap}, L) ->
  lists:foldr(fun tvs_list/2, L, maps:values(FieldMap));
tvs_list({record_ext, _, Ext, BaseT}, L) ->
  tvs_list({record, none, Ext}, tvs_list(BaseT, L));
tvs_list({hole, _}, L) -> L.

args_ivs(T) -> args_ivs(T, ordsets:new()).

args_ivs({lam, ArgTs, ReturnT}, InitSeenVs) ->
  case length(ArgTs) of
    0 -> [ivs(ReturnT, InitSeenVs)];
    Length ->
      {ExceptLast, [LastT]} = lists:split(Length - 1, ArgTs),
      LastIVs = ivs({tuple, [LastT, ReturnT]}, InitSeenVs),
      [ivs(ArgT, InitSeenVs) || ArgT <- ExceptLast] ++ [LastIVs]
  end.

family_is("Ord", _) -> ordsets:from_list(["Ord"]);
family_is("Num", _) -> ordsets:from_list(["Num", "Ord"]);
family_is(I, Ifaces) ->
  {_, _, Parents} = maps:get(I, Ifaces),
  ordsets:fold(fun(ParentI, Family) ->
    ordsets:union(Family, family_is(ParentI, Ifaces))
  end, ordsets:add_element(I, Parents), Parents).

test_names(Module, GEnv) ->
  maps:fold(fun
    ({M, Name}, #binding{inst={con, "Test"}}, Set) when M == Module ->
      ordsets:add_element(Name, Set);
    (_, _, Set) -> Set
  end, ordsets:new(), GEnv).

exported_idents(Module, Loc, #ctx{exports=Exports}) ->
  Names = maps:get(Module, Exports),
  lists:map(fun
    ([H | _]=Name) when H >= $a andalso H =< $z -> {var, Loc, Name};
    (Name) -> {con_token, Loc, Name}
  end, ordsets:to_list(Names)).

prep_compiled(Compiled, Dir) ->
  lists:foreach(fun
    ({compiled, Mod, Binary}) ->
      Path = filename:join(Dir, atom_to_list(Mod) ++ ".beam"),
      ok = file:write_file(Path, Binary),
      utils:remove_mod(Mod);

    ({precompiled, Mod, Existing}) ->
      Path = filename:join(Dir, atom_to_list(Mod) ++ ".beam"),
      {ok, _} = file:copy(Existing, Path),
      utils:remove_mod(Mod)
  end, Compiled),

  {compiled, Mod, _} = hd(Compiled),
  code:add_patha(Dir),
  par_native:init(Mod),
  Mod.

remove_compiled(Compiled, Dir) ->
  % Must explicitly remove all modules. Some of these modules are from *new*
  % stdlibs. We don't want the old parser/lexer to use new stdlibs.
  [utils:remove_mod(Mod) || {Mod, _} <- Compiled],
  code:del_path(Dir).

  % TODO: is this necessary? can we remove?
  % We need to re-initialize the parser; otherwise, the gm can contain
  % references to funs from the stdlib modules that were just removed.
  %% par_native:init('Par.Parser').

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

% TODO: use iolists for efficiency
pretty({lam, ArgTs, ReturnT}) ->
  case ArgTs of
    [] -> ?FMT("() -> ~s", [pretty(ReturnT)]);
    [ArgT] when element(1, ArgT) == lam; element(1, ArgT) == tuple ->
      ?FMT("(~s) -> ~s", [pretty(ArgT), pretty(ReturnT)]);
    [ArgT] -> ?FMT("~s -> ~s", [pretty(ArgT), pretty(ReturnT)]);
    _ ->
      PrettyArgTs = string:join([pretty(ArgT) || ArgT <- ArgTs], ", "),
      ?FMT("(~s) -> ~s", [PrettyArgTs, pretty(ReturnT)])
  end;
pretty({lam, _, Provided, ReturnT}) ->
  pretty({lam, [T || {_, _, T} <- Provided], ReturnT});
pretty({tuple, ElemTs}) ->
  PrettyElemTs = string:join([pretty(ElemT) || ElemT <- ElemTs], ", "),
  ?FMT("(~s)", [PrettyElemTs]);
pretty({tv, RawV, Is, _}) ->
  % all generated Vs are prefixed with *, but user-inputted ones in signatures
  % lack the leading *
  V = case RawV of
    [$* | T] -> T;
    _ -> RawV
  end,
  if
    Is == none -> V;
    true ->
      Unqualified = lists:map(fun(I) ->
        utils:unqualify(I)
      end, ordsets:to_list(Is)),
      ?FMT("~s ~~ ~s", [V, string:join(Unqualified, " ~ ")])
  end;
pretty({set_ifaces, Is}) ->
  Unqualified = lists:map(fun(I) ->
    utils:unqualify(I)
  end, ordsets:to_list(Is)),
  ?FMT("set_ifaces(~s)", [string:join(Unqualified, " ~ ")]);
pretty({set_ifaces_rigid, Is}) ->
  Unqualified = lists:map(fun(I) ->
    utils:unqualify(I)
  end, ordsets:to_list(Is)),
  ?FMT("set_ifaces_rigid(~s)", [string:join(Unqualified, " ~ ")]);
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
        true -> ordsets:union(Is, BaseIs)
      end,
      {pretty({tv, V, none, Rigid}), MergedIs};

    _ -> {pretty(BaseT), Is}
  end,

  PrettyIs = case AllIs of
    none -> "";
    _ ->
      Unqualified = lists:map(fun(I) ->
        utils:unqualify(I)
      end, ordsets:to_list(AllIs)),
      ?FMT(" ~~ ~s", [string:join(Unqualified, " ~ ")])
  end,
  ?FMT("~s<~s>~s", [PrettyBaseT, string:join(PrettyParamTs, ", "), PrettyIs]);
pretty({inst, _, TV}) -> ?FMT("inst(~s)", [pretty(TV)]);
pretty({inst, _, GVs, T}) ->
  ?FMT("inst(~s, ~p)", [pretty(T), ordsets:to_list(GVs)]);
pretty({record, _, FieldMap}) -> ?FMT("{ ~s }", [pretty_field_map(FieldMap)]);
pretty({record_ext, _, Ext, BaseT}) ->
  ?FMT("{ ~s | ~s }", [pretty_field_map(Ext), pretty(BaseT)]);
pretty({hole, _}) -> "_".

pretty_field_map(FieldMap) ->
  FieldStrs = maps:fold(fun(Name, T, Strs) ->
    [?FMT("~s : ~s", [Name, pretty(T)]) | Strs]
  end, [], FieldMap),
  string:join(lists:sort(FieldStrs), ", ").

temp_dir() ->
  Bytes = crypto:strong_rand_bytes(16),
  Dir = filename:join(os:getenv("TEMP", "/tmp"), "par-" ++ hex_encode(Bytes)),
  case file:make_dir(Dir) of
    ok -> Dir;
    {error, eexist} -> temp_dir()
  end.

hex_encode(<<>>) -> [];
hex_encode(<<H, T/binary>>) ->
  case integer_to_list(H, 16) of
    [A, B] -> [A, B | hex_encode(T)];
    [A] -> [$0, A | hex_encode(T)]
  end.

remove_mod(Mod) ->
  code:purge(Mod),
  code:delete(Mod),
  code:purge(Mod).
