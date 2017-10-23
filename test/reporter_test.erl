-module(reporter_test).

-include_lib("eunit/include/eunit.hrl").

-define(TMP_MANY_DIR, "/tmp/reporter-test-many").

-define(
  golden_expr_(Name, Expr),
  {?LINE, fun() ->
    Errors = type_system_test:type_check("expr =\n" ++ Expr),
    ?assertNot(is_tuple(Errors) andalso element(1, Errors) == ok),
    Str = lists:flatten(reporter:format(Errors)),
    check(Name, Str)
  end}
).

-define(
  golden_prg_(Name, Prg),
  {?LINE, fun() ->
    Errors = type_system_test:type_check(Prg),
    ?assertNot(is_tuple(Errors) andalso element(1, Errors) == ok),
    Str = lists:flatten(reporter:format(Errors)),
    check(Name, Str)
  end}
).

-define(
  golden_many_(Name, PathPrgs, TargetPath),
  {?LINE, fun() ->
    Errors = type_system_test:type_check_many(
      ?TMP_MANY_DIR,
      PathPrgs,
      TargetPath
    ),
    ?assertNot(is_tuple(Errors) andalso element(1, Errors) == ok),
    Str = lists:flatten(reporter:format(Errors)),
    check(Name, Str)
  end}
).

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
  % lexer errors
  [ ?golden_expr_("l-bad-char", "let a = ^3\na")
  , ?golden_expr_("l-unterminated-string-1", "(\"hello world, true)")
  , ?golden_expr_("l-unterminated-string-2", "\"hello, \nworld\"")
  , ?golden_expr_("l-bad-atom", "@+asdf")
  , ?golden_expr_("l-bad-var", "a?b + 3")
  , ?golden_expr_("l-multiple-dots", "3.07.8")
  , ?golden_many_("l-multiple-modules-errors", [
      {"foo",
        "module Foo\n"
        "import \"./bar\"\n"
        "import \"./baz\"\n"
        "a = 1"
      },
      {"bar",
        "module Bar\n"
        "a = `something`"
      },
      {"baz",
        "module Baz\n"
        "a = @\"hi"
      }
    ], "foo")

  % parser errors
  , ?golden_expr_("p-list-literal", "[@a @b]")
  , ?golden_expr_("p-let-misaligned-1", "let x = 3\n  x + 5")
  , ?golden_expr_("p-let-misaligned-2", "  let x = \n3 x + 5")
  , ?golden_expr_("p-block-misaligned-1", "3 + 5\n  @hello")
  , ?golden_expr_("p-block-misaligned-2", "  3 + \n5 @hello")
  , ?golden_expr_("p-record-misaligned-1", "{ a = 3\nbar = true }")
  , ?golden_expr_("p-record-misaligned-2", "{ a = \n3 bar = true }")
  , ?golden_expr_("p-list-misaligned-1", "[ -5\n@hello ]")
  , ?golden_expr_("p-list-misaligned-2", "[ -\n5 @hello ]")
  , ?golden_expr_("p-list-let", "[3\n let x = 4\n 5]")
  , ?golden_expr_("p-list-block-comma", "[foo\n 'b',\n \"hi\"]")
  , ?golden_expr_("p-bad-map", "{ @hello, 3 + 5 }")
  , ?golden_expr_("p-bad-tuple", "(1,)")
  , ?golden_expr_("p-bad-tuple-te", "(1, @hi) : (Int,)")
  , ?golden_expr_("p-bad-tuple-pattern", "let (1,) = (1, @hi)\n2")
  , ?golden_expr_("p-no-closing-1", "{ a = 3")
  , ?golden_expr_("p-no-closing-2", "[1, [2, [3, 4], 5, 6]")
  , ?golden_expr_("p-native", "erlang:length([])")
  , ?golden_prg_(
      "p-enum-comma-newline-1",
      "enum SumType {\n"
      "  Foo,\n"
      "  Bar(String) @bar\n"
      "}"
    )
  , ?golden_prg_(
      "p-enum-comma-newline-2",
      "enum SumType { Foo\n"
      "             , Bar(String) @bar\n"
      "             }"
    )
  , ?golden_prg_(
      "p-enum-comma-newline-4",
      "enum SumType<A> {\n"
      "  Foo(A) Bar\n"
      "}"
    )
  , ?golden_prg_(
      "p-struct-comma-newline-1",
      "struct ProductType {\n"
      "  foo : Foo,\n"
      "  bar : String\n"
      "}"
    )
  , ?golden_prg_(
      "p-struct-comma-newline-2",
      "struct ProductType { foo : Foo\n"
      "                   , bar : String\n"
      "                   }"
    )
  , ?golden_prg_(
      "p-struct-comma-newline-4",
      "struct ProductType<A> {\n"
      "  foo : A bar : Atom\n"
      "}"
    )
  , ?golden_prg_("p-enum-tv", "enum T { Foo }")
  , ?golden_prg_("p-struct-tv", "struct T { foo : Int }")
  , ?golden_prg_(
      "p-impl-tv",
      "interface Foo { a : T -> Int }\n"
      "impl Foo for A { a(_) = 3 }"
    )
  , ?golden_prg_(
      "p-impl-gen-tv",
      "interface Foo { a : T -> Int }\n"
      "impl Foo for T<A> { a(_) = 3 }"
    )
  , ?golden_prg_("p-impl-name", "impl [A] for Foo { foo(_) = 1 }")
  , ?golden_prg_(
      "p-bad-import",
      "import List (315)\n"
      "a = 1"
    )
  , ?golden_prg_(
      "p-bad-import-all",
      "import List (foo, *)\n"
      "a = 1"
    )
  , ?golden_many_("p-multiple-modules-errors", [
      {"foo",
        "module Foo\n"
        "import \"./bar\"\n"
        "import \"./baz\"\n"
        "a = 1"
      },
      {"bar",
        "module Bar\n"
        "a b = 3"
      },
      {"baz",
        "module Baz\n"
        "a(x y z) = *4.5"
      }
    ], "foo")

  % lexer and parser errors
  , ?golden_many_("lp-multiple-modules-errors", [
      {"foo",
        "module Foo\n"
        "import \"./bar\"\n"
        "import \"./baz\"\n"
        "a = 1"
      },
      {"bar",
        "module Bar\n"
        "a = `14.153.0"
      },
      {"baz",
        "module Baz\n"
        "a(x y z) = *4.5"
      }
    ], "foo")

  % read/import errors
  , ?golden_many_("read", [], "foo")
  , ?golden_many_("import", [
      {"foo",
        "module Foo\n"
        "import \"./bar\"\n"
        "a = 1"
      }
    ], "foo")

  % type system errors
  , ?golden_expr_("ts-mismatch", "true + 5")
  , ?golden_expr_("ts-other", "let a = 3\n(a, true, b)")
  , ?golden_expr_("ts-order", "let a = 3 : Bool\na.field")
  , ?golden_expr_("ts-extra-args-lam", "(|x| x)(true, @hi)")
  , ?golden_expr_(
      "ts-extra-args-recursive",
      "let f(x) = if x == 0 then 0 else f(x - 1)\nf(2, 3)"
    )
  , ?golden_prg_(
      "ts-extra-args-fn",
      "f(x) = if x == 0 then 0 else f(x - 1)\n"
      "expr = f(2, 3)"
    )
  , ?golden_prg_(
      "ts-rhs-pipe",
      "f(a, b) = a ++ b\n"
      "expr = \"bye\" |> f(\"hey\", \"hi\")"
    )
  , ?golden_prg_(
      "ts-extra-args-pipe",
      "f(a, b) = a ++ b\n"
      "expr = \"bye\" |> f(\"hey\", \"hi\", \"hello\")"
    )
  , ?golden_many_("ts-multiple-modules-errors", [
      {"foo",
        "module Foo\n"
        "import \"./bar\"\n"
        "export a = 'c'\n"
        "b = Bar.d(true)\n"
        "c = Bar.d(1, 2, 3)"
      },
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "export d(x) = [1, x]\n"
        "e = [Foo.a] ++ \"hi\"\n"
        "f = match Foo.a {\n"
        "  1 => 3\n"
        "}"
      }
    ], "foo")
  ].
