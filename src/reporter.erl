-module(reporter).
-export([format/1]).

-include("common.hrl").
-define(LINE_WIDTH, 80).

format([Err | Errs]) -> [format(Err) | format(Errs)];
format([]) -> [];

format({read_error, Path, Reason}) ->
  Msg = ?FMT("Couldn't read file ~s: ~s", [Path, reason_str(Reason)]),
  [wrap(Msg, ?LINE_WIDTH), $\n];

format({import_error, Loc, ImportPath, Reason, Comp}) ->
  #comp{module=Module, path=Path, prg=Prg} = Comp,
  Prefix = ?FMT("*** module ~s *** (~s)~n~n", [Module, Path]),

  StrLines = split_lines(Prg),
  Code = extract_code(Loc, StrLines),

  Msg = ?FMT("Couldn't import ~s: ~s", [ImportPath, reason_str(Reason)]),
  [Prefix, wrap(Msg, ?LINE_WIDTH), $:, $\n, Code, $\n];

format({lexer_errors, Errs, Path, Prg}) ->
  StrLines = split_lines(Prg),
  Prefix = ?FMT("*** file ~s ***~n~n", [Path]),

  SortedErrs = lists:sort(fun(Err1, Err2) ->
    {unexpected, Loc1, _, _} = Err1,
    {unexpected, Loc2, _, _} = Err2,
    loc_lte(Loc1, Loc2)
  end, Errs),

  StrErrs = lists:map(fun({unexpected, Loc, _, Msg}) ->
    Code = extract_code(Loc, StrLines),
    [wrap(Msg, ?LINE_WIDTH), $:, $\n, Code, $\n]
  end, SortedErrs),

  [Prefix, StrErrs];

format({parser_errors, Errs, Path, Prg}) ->
  StrLines = split_lines(Prg),
  Prefix = ?FMT("*** file ~s ***~n~n", [Path]),

  LastLine = array:size(StrLines),
  LastCol = length(array:get(LastLine - 1, StrLines)),

  EndLoc = #{
    start_line => LastLine,
    start_col => LastCol,
    end_line => LastLine,
    end_col => LastCol + 1
  },

  SortedErrs = lists:sort(fun({MaybeLoc1, _}, {MaybeLoc2, _}) ->
    Loc1 = case MaybeLoc1 of
      none -> EndLoc;
      {some, Loc1_} -> Loc1_
    end,
    Loc2 = case MaybeLoc2 of
      none -> EndLoc;
      {some, Loc2_} -> Loc2_
    end,
    loc_lte(Loc1, Loc2)
  end, Errs),

  StrErrs = lists:map(fun({MaybeLoc, Msg}) ->
    case MaybeLoc of
      none ->
        Suffixed = binary_to_list(Msg) ++ " before end-of-file.",
        [wrap(Suffixed, ?LINE_WIDTH), $\n, $\n];
      {some, Loc} ->
        Code = extract_code(Loc, StrLines),
        [wrap(Msg, ?LINE_WIDTH), $:, $\n, Code, $\n]
    end
  end, SortedErrs),

  [Prefix, StrErrs];

format({errors, Errs, Comps}) ->
  Pairs = lists:map(fun(#comp{module=Module, path=Path, prg=Prg}) ->
    {Module, {Path, split_lines(Prg)}}
  end, Comps),

  ModuleMap = maps:from_list(Pairs),
  SortedErrs = lists:sort(fun type_system_err_lte/2, Errs),

  {StrErrs, _} = lists:mapfoldl(fun(Err, LastModule) ->
    {Module, Loc} = case Err of
      {_, _, Module_, Loc_, _} -> {Module_, Loc_};
      {_, Module_, Loc_} -> {Module_, Loc_}
    end,
    {Path, StrLines} = maps:get(Module, ModuleMap),

    Prefix = if
      Module /= LastModule ->
        ?FMT("*** module ~s *** (~s)~n~n", [Module, Path]);
      true -> ""
    end,
    Code = extract_code(Loc, StrLines),

    Str = case Err of
      {{lam, _, _, _, _}=T1, {lam, _, _}=T2, _, _, From} ->
        format_arity(T1, T2, From);
      {{lam, _, _}=T1, {lam, _, _, _, _}=T2, _, _, From} ->
        format_arity(T2, T1, From);

      {T1, T2, _, _, From} ->
        Msg = ?FMT(
          "Mismatched types ~s and ~s from ~s",
          [utils:pretty(T1), utils:pretty(T2), From]
        ),
        [wrap(Msg, ?LINE_WIDTH), $:, $\n];

      {Msg, _, _} -> [wrap(Msg, ?LINE_WIDTH), $:, $\n]
    end,

    {[Prefix, Str, Code, $\n], Module}
  end, none, SortedErrs),

  StrErrs.

reason_str(enoent) -> "file doesn't exist";
reason_str(eaccess) -> "don't have necessary permissions";
reason_str(eisdir) -> "file is a directory";
reason_str(enotdir) -> "one of the directories in the path doesn't exist";
reason_str(enomem) -> "not enough memory";
reason_str(Err) -> ?FMT("unknown error: ~p", Err).

split_lines(Prg) -> array:from_list(re:split(Prg, "\r?\n", [{return, list}])).

wrap(Str, Width) ->
  Words = re:split(Str, " ", [{return, list}]),
  wrap(Words, Width, 0, []).

wrap([], _, _, Accum) -> lists:reverse(tl(Accum));
wrap([Word | Words], Width, Length, Accum) ->
  % extra 1 for whitespace after
  WordLength = length(Word) + 1,

  if
    Length + WordLength > Width ->
      wrap(Words, Width, WordLength, [$\s, Word, $\n | Accum]);
    true ->
      wrap(Words, Width, Length + WordLength, [$\s, Word | Accum])
  end.

format_arity(T1, T2, From) ->
  GivenArity = given_arity(T1),
  NeedArity = max_arity(T2),

  true = GivenArity > NeedArity,
  Plural = case NeedArity of
    1 -> "";
    _ -> "s"
  end,

  ?FMT(
    "From ~s, given ~p arguments, but need at most ~p argument~s:~n",
    [From, GivenArity, NeedArity, Plural]
  ).

given_arity(T) -> given_arity(T, 0).
given_arity({lam, _, _, _, ReturnT}, Arity) -> given_arity(ReturnT, Arity + 1);
given_arity(_, Arity) -> Arity.

max_arity(T) -> max_arity(T, 0).
max_arity({lam, _, ReturnT}, Arity) -> max_arity(ReturnT, Arity + 1);
max_arity({lam, _, _, _, ReturnT}, Arity) -> max_arity(ReturnT, Arity + 1);
max_arity(_, Arity) -> Arity.

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

extract_code(Loc, StrLines) ->
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

      % end column is exclusive, so we subtract 1
      Underline = string:right(Carets, length(Prefix) + EndCol - 1),
      StrLine = array:get(StartLine - 1, StrLines),

      io_lib:format(
        "~s~s~n"
        "~s~n",
        [Prefix, StrLine, Underline]
      );

    true ->
      lists:map(fun(Line) ->
        StrLine = array:get(Line - 1, StrLines),
        io_lib:format("~p: ~s~n", [Line, StrLine])
      end, lists:seq(StartLine, EndLine))
  end.

