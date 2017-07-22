-module(reporter_test).

-include_lib("eunit/include/eunit.hrl").

-define(TMP_MANY_DIR, "/tmp/reporter-test-many").

golden_expr_(Name, Expr) ->
  fun() ->
    {errors, _, _}=Errors = type_system_test:type_check("expr = " ++ Expr),
    Str = lists:flatten(reporter:format(Errors)),
    check(Name, Str)
  end.

golden_prg_(Name, Prg) ->
  fun() ->
    {errors, _, _}=Errors = type_system_test:type_check(Prg),
    Str = lists:flatten(reporter:format(Errors)),
    check(Name, Str)
  end.

golden_many_(Name, PathPrgs, TargetPath) ->
  fun() ->
    {errors, _, _}=Errors = type_system_test:type_check_many(
      ?TMP_MANY_DIR,
      PathPrgs,
      TargetPath
    ),
    Str = lists:flatten(reporter:format(Errors)),
    check(Name, Str)
  end.

check(Name, Str) ->
  {ok, Dir} = file:get_cwd(),
  Path = filename:join([Dir, "test", "golden", "reporter-" ++ Name]),

  case init:get_argument(update) of
    {ok, _} ->
      io:format(user, "updated golden file ~p~n", [Name]),
      ?assertEqual(ok, file:write_file(Path, Str));
    error ->
      case file:read_file(Path) of
        {ok, Binary} -> ?assertEqual(binary_to_list(Binary), Str);
        _ ->
          io:format("~s", [Str]),
          ?assert(false)
      end
  end.

expr_test_() ->
  [ golden_expr_("mismatch", "true + 5")
  , golden_expr_("other", "let a = 3 in (a, true, b)")
  , golden_expr_("order", "let a = 3 :: Bool in a.field")
  , golden_expr_("extra-args-lam", "(|x| x)(true, @hi)")
  , golden_expr_(
      "extra-args-recursive",
      "let f(x) = if x == 0 then 0 else f(x - 1) in f(2, 3)"
    )
  , golden_prg_(
      "extra-args-fn",
      "f(x) = if x == 0 then 0 else f(x - 1)\n"
      "expr = f(2, 3)"
    )
  , golden_prg_(
      "rhs-pipe",
      "f(a, b) = a ++ b\n"
      "expr = \"bye\" |> f(\"hey\", \"hi\")"
    )
  , golden_prg_(
      "extra-args-pipe",
      "f(a, b) = a ++ b\n"
      "expr = \"bye\" |> f(\"hey\", \"hi\", \"hello\")"
    )
  , golden_many_("multiple-modules-errors", [
      {"foo",
        "module Foo\n"
        "import \"./bar\"\n"
        "export a = 'c'\n"
        "b = Bar.d(true)\n"
        "c = Bar.d(1, 2, 3)"},
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "export d(x) = [1, x]\n"
        "e = [Foo.a] ++ \"hi\"\n"
        "f = match Foo.a {\n"
        "  1 => 3\n"
        "}"}
    ], "foo")
  ].
