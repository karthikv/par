-module(reporter).
-export([format/1, format/3, norm/3, extract_snippet/2]).

-include("common.hrl").
-define(LINE_WIDTH, 80).

format([Err | Errs]) -> [format(Err) | format(Errs)];
format([]) -> [];

format({read_error, Path, Reason}) ->
  Msg = ?FMT("Couldn't read file ~s: ~s", [Path, reason_str(Reason)]),
  [wrap(Msg, ?LINE_WIDTH), $\n];

format({import_error, Loc, PathOrCon, Reason, Comp}) ->
  #comp{module=Module, path=Path, prg_lines=PrgLines} = Comp,
  Prefix = ?FMT("*** module ~s *** (~s)~n~n", [Module, Path]),
  Code = extract_code(Loc, PrgLines),

  Msg = ?FMT("Couldn't import ~s: ~s", [PathOrCon, reason_str(Reason)]),
  [Prefix, wrap(Msg, ?LINE_WIDTH), $:, $\n, $\n, Code, $\n];

format({lexer_errors, Errs, Path, PrgLines}) ->
  Prefix = ?FMT("*** file ~s ***~n~n", [Path]),
  SortedErrs = lists:sort(fun(Err1, Err2) ->
    {unexpected, Loc1, _, _} = Err1,
    {unexpected, Loc2, _, _} = Err2,
    loc_lte(Loc1, Loc2)
  end, Errs),

  StrErrs = lists:map(fun({unexpected, Loc, _, Msg}) ->
    Code = extract_code(Loc, PrgLines),
    [wrap(Msg, ?LINE_WIDTH), $:, $\n, $\n, Code, $\n]
  end, SortedErrs),

  [Prefix, StrErrs];

format({parser_errors, Errs, Path, PrgLines}) ->
  Prefix = ?FMT("*** file ~s ***~n~n", [Path]),
  LastLine = array:size(PrgLines),
  LastCol = length(array:get(LastLine - 1, PrgLines)),

  EndLoc = #{
    start_line => LastLine,
    start_col => LastCol,
    end_line => LastLine,
    end_col => LastCol + 1
  },

  SortedErrs = lists:sort(fun({MaybeLoc1, _}, {MaybeLoc2, _}) ->
    Loc1 = case MaybeLoc1 of
      'None' -> EndLoc;
      {'Some', Loc1_} -> Loc1_
    end,
    Loc2 = case MaybeLoc2 of
      'None' -> EndLoc;
      {'Some', Loc2_} -> Loc2_
    end,
    loc_lte(Loc1, Loc2)
  end, Errs),

  StrErrs = lists:map(fun({MaybeLoc, Msg}) ->
    case MaybeLoc of
      'None' ->
        Suffixed = unicode:characters_to_list(Msg) ++ " before end-of-file.",
        [wrap(Suffixed, ?LINE_WIDTH), $\n, $\n];
      {'Some', Loc} ->
        Code = extract_code(Loc, PrgLines),
        [wrap(Msg, ?LINE_WIDTH), $:, $\n, $\n, Code, $\n]
    end
  end, SortedErrs),

  [Prefix, StrErrs];

format({errors, Errs, Comps}) ->
  CompMapPairs = lists:map(fun(#comp{module=Module}=Comp) ->
    {Module, Comp}
  end, Comps),

  CompMap = maps:from_list(CompMapPairs),
  SortedErrs = lists:sort(fun type_system_err_lte/2, Errs),

  {StrErrs, _} = lists:mapfoldl(fun(Err, LastModule) ->
    {Msg, Module, Loc} = Err,
    #comp{path=Path}=Comp = maps:get(Module, CompMap),

    Prefix = if
      Module /= LastModule ->
        ?FMT("*** module ~s *** (~s)~n~n", [Module, Path]);
      true -> ""
    end,

    Formatted = format(Msg, Loc, Comp),
    {[Prefix, wrap(Formatted, ?LINE_WIDTH)], Module}
  end, none, SortedErrs),

  StrErrs.

format(Msg, Loc, #comp{prg_lines=PrgLines}) ->
  {ok, Pid} = tv_server:start_link(),
  {Parts, _} = lists:mapfoldl(fun
    (OtherLoc, Subs) when is_map(OtherLoc) ->
      {[$:, $\n, $\n, extract_code(OtherLoc, PrgLines), $\n], Subs};

    (T, Subs) when is_tuple(T) ->
      {NormT, NewSubs} = norm(T, Subs, Pid),
      {utils:pretty(NormT), NewSubs};

    (Arg, Subs) -> {Arg, Subs}
  end, #{}, Msg),

  ok = tv_server:stop(Pid),
  IOList = [Parts, [$:, $\n, $\n, extract_code(Loc, PrgLines), $\n]],
  lists:flatten(IOList).

norm(T, Subs, Pid) ->
  NewSubs = lists:foldl(fun
    ({tv, V, _, _}, FoldSubs) ->
      case maps:is_key(V, FoldSubs) of
        true -> FoldSubs;
        false -> FoldSubs#{V => tv_server:next_name(Pid)}
      end;
    (_, FoldSubs) -> FoldSubs
  end, Subs, utils:tvs_list(T)),

  {utils:subs(T, #sub_opts{subs=NewSubs, shallow=true}), NewSubs}.

% pass strings through w/o modification
reason_str(Str) when is_list(Str) -> Str;
reason_str(Err) -> file:format_error(Err).

wrap(Str, Width) ->
  {ok, CodeRegex} = re:compile("^\\s*(\\d+:|\\^+)", [no_auto_capture]),
  Lines = re:split(Str, "(\n)", [{return, list}]),

  lists:map(fun(Line) ->
    if
      Line == "\n"; Line == [] -> Line;
      true ->
        case re:run(Line, CodeRegex) of
          {match, _} -> Line;
          nomatch ->
            Words = re:split(Line, " ", [{return, list}]),
            wrap(Words, Width, 0, [])
        end
    end
  end, Lines).

wrap([], _, _, Accum) -> lists:reverse(tl(Accum));
wrap([Word | Words], Width, Length, Accum) ->
  % extra 1 for whitespace after
  WordLength = length(Word) + 1,

  if
    Length + WordLength > Width ->
      % Use tl(Accum) to remove extra whitespace at end of line.
      wrap(Words, Width, WordLength, [$\s, Word, $\n | tl(Accum)]);
    true ->
      wrap(Words, Width, Length + WordLength, [$\s, Word | Accum])
  end.

type_system_err_lte(Err1, Err2) ->
  {Module1, Loc1} = case Err1 of
    {_, _, Module1_, Loc1_, _} -> {Module1_, Loc1_};
    {_, Module1_, Loc1_} -> {Module1_, Loc1_}
  end,
  {Module2, Loc2} = case Err2 of
    {_, _, Module2_, Loc2_, _} -> {Module2_, Loc2_};
    {_, Module2_, Loc2_} -> {Module2_, Loc2_}
  end,

  if
    Module1 /= Module2 -> Module1 < Module2;
    true -> loc_lte(Loc1, Loc2)
  end.

% A builtin loc shouldn't happen, but we handle this case so we can still see an
% output from the reporter.
loc_lte(?BUILTIN_LOC, _) -> true;
loc_lte(_, ?BUILTIN_LOC) -> false;
loc_lte(Loc1, Loc2) ->
  #{
    start_line := StartLine1,
    start_col := StartCol1,
    end_line := EndLine1,
    end_col := EndCol1
  } = Loc1,
  #{
    start_line := StartLine2,
    start_col := StartCol2,
    end_line := EndLine2,
    end_col := EndCol2
  } = Loc2,

  if
    StartLine1 /= StartLine2 -> StartLine1 < StartLine2;
    StartCol1 /= StartCol2 -> StartCol1 < StartCol2;
    EndLine1 /= EndLine2 -> EndLine1 < EndLine2;
    true -> EndCol1 =< EndCol2
  end.

% A builtin loc shouldn't happen, but we handle this case so we can still see an
% output from the reporter.
extract_code(?BUILTIN_LOC, _) -> "(builtin code)";
extract_code(Loc, PrgLines) ->
  #{
    start_line := StartLine,
    start_col := StartCol,
    end_line := EndLine,
    end_col := EndCol
  } = Loc,

  if
    StartLine == EndLine ->
      Carets = string:copies("^", EndCol - StartCol),
      Prefix = ?FMT("~p: ", [StartLine]),

      PrgLine = array:get(StartLine - 1, PrgLines),
      Trimmed = string:strip(PrgLine, left),
      TrimmedLength = length(PrgLine) - length(Trimmed),

      % end column is exclusive, so we subtract 1
      Offset = length(Prefix) + EndCol - 1 - TrimmedLength,
      Underline = string:right(Carets, Offset),

      io_lib:format(
        "~s~s~n"
        "~s~n",
        [Prefix, Trimmed, Underline]
      );

    true ->
      lists:map(fun(Line) ->
        PrgLine = array:get(Line - 1, PrgLines),
        io_lib:format("~p: ~s~n", [Line, PrgLine])
      end, lists:seq(StartLine, EndLine))
  end.

extract_snippet(Loc, PrgLines) ->
  #{
    start_line := StartLine,
    start_col := StartCol,
    end_line := EndLine,
    end_col := EndCol
  } = Loc,

  StartPrgLine = array:get(StartLine - 1, PrgLines),

  if
    StartLine == EndLine ->
      lists:sublist(StartPrgLine, StartCol, EndCol - StartCol);

    true ->
      Start = lists:sublist(StartPrgLine, StartCol, length(StartPrgLine)),
      Middle = lists:flatmap(fun(Line) ->
        [array:get(Line - 1, PrgLines), $\n]
      end, lists:seq(StartLine + 1, EndLine - 1)),

      EndPrgLine = array:get(EndLine - 1, PrgLines),
      % end column is exclusive, so we subtract 1
      End = lists:sublist(EndPrgLine, EndCol - 1),

      lists:flatten([Start, $\n, Middle, End])
  end.
