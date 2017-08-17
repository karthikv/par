-module(utils).
-export([unqualify/1, absolute/1, pretty_csts/1, pretty/1]).
-include("errors.hrl").

unqualify(Con) ->
  case string:chr(Con, $.) of
    0 -> Con;
    Index -> lists:sublist(Con, Index + 1, length(Con))
  end.

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
pretty({tv, RawV, I, Rigid}) ->
  % all generated Vs are prefixed with *, but user-inputted ones in signatures
  % lack the leading *
  V = case RawV of
    [$* | T] -> T;
    _ -> RawV
  end,
  Str = if
    I == none -> V;
    true -> ?FMT("~s: ~s", [V, utils:unqualify(I)])
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
pretty(none) -> "()".

pretty_field_map(FieldMap) ->
  FieldStrs = maps:fold(fun(Name, T, Strs) ->
    [?FMT("~s : ~s", [Name, pretty(T)]) | Strs]
  end, [], FieldMap),
  string:join(lists:sort(FieldStrs), ", ").
