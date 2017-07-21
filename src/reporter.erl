-module(reporter).
-export([report_errors/1]).
-include("errors.hrl").

report_errors({errors, Errs, Comps}) ->
  {ok, LineRegex} = re:compile("\r?\n"),
  SplitOpts = [{return, list}],

  Pairs = lists:map(fun(#comp{module=Module, path=Path, contents=Contents}) ->
    StrLines = re:split(Contents, LineRegex, SplitOpts),
    {Module, {Path, array:from_list(StrLines)}}
  end, Comps),
  ModuleMap = maps:from_list(Pairs),

  SortedErrs = lists:sort(fun err_lte/2, Errs),

  {StrErrs, _} = lists:mapfoldl(fun(Err, LastModule) ->
    {Module, Loc} = case Err of
      {_, _, Module_, Loc_, _} -> {Module_, Loc_};
      {_, Module_, Loc_} -> {Module_, Loc_}
    end,
    {Path, StrLinesArray} = maps:get(Module, ModuleMap),

    Prefix = if
      Module /= LastModule ->
        ?FMT("*** module ~s *** (~s)~n~n", [Module, Path]);
      true -> ""
    end,
    Code = extract_code(Loc, StrLinesArray),

    case Err of
      {{lam, _, _, _}=T1, {lam, _, _}=T2, _, _, From} ->
        {report_arg_count(Prefix, T1, T2, From, Code), Module};
      {{lam, _, _}=T1, {lam, _, _, _}=T2, _, _, From} ->
        {report_arg_count(Prefix, T2, T1, From, Code), Module};

      {T1, T2, _, _, From} ->
        Str = ?FMT(
          "~s"
          "Mismatched types ~s and ~s from ~s:~n"
          "~s~n",
          [Prefix, type_system:pretty(T1), type_system:pretty(T2), From, Code]
        ),
        {Str, Module};

      {Msg, _, _} ->
        Str = ?FMT(
          "~s"
          "~s:~n"
          "~s~n",
          [Prefix, Msg, Code]
        ),
        {Str, Module}
    end
  end, none, SortedErrs),

  ?ERR("~s", [StrErrs]).

report_arg_count(Prefix, T1, T2, From, Code) ->
  GivenArity = given_arity(T1),
  NeedArity = max_arity(T2),

  true = GivenArity > NeedArity,
  Plural = case NeedArity of
    1 -> "";
    _ -> "s"
  end,

  ?FMT(
    "~s"
    "From ~s, given ~p arguments, but need at most ~p argument~s:~n"
    "~s~n",
    [Prefix, From, GivenArity, NeedArity, Plural, Code]
  ).

given_arity(T) -> given_arity(T, 0).
given_arity({lam, _, _, ReturnT}, Arity) -> given_arity(ReturnT, Arity + 1);
given_arity(_, Arity) -> Arity.

max_arity(T) -> max_arity(T, 0).
max_arity({lam, _, ReturnT}, Arity) -> max_arity(ReturnT, Arity + 1);
max_arity({lam, _, _, ReturnT}, Arity) -> max_arity(ReturnT, Arity + 1);
max_arity(_, Arity) -> Arity.

err_lte(Err1, Err2) ->
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
    true ->
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
      end
  end.

extract_code(Loc, StrLinesArray) ->
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
      StrLine = array:get(StartLine - 1, StrLinesArray),

      io_lib:format(
        "~s~s~n"
        "~s~n",
        [Prefix, StrLine, Underline]
      );

    true ->
      lists:map(fun(Line) ->
        StrLine = array:get(Line - 1, StrLinesArray),
        io_lib:format("~p: ~s~n", [Line, StrLine])
      end, lists:seq(StartLine, EndLine))
  end.

