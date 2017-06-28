-module(utils).
-export([unqualify/1, absolute/1]).

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
