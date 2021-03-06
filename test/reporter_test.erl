-module(reporter_test).

-include_lib("eunit/include/eunit.hrl").
-include("../src/common.hrl").

check_has_errors(Result) when element(1, Result) == ok ->
  io:format("Expected errors, but got valid program~n"),
  ?assert(false);
check_has_errors(_) -> ok.

-define(
  golden_expr_(Name, Expr),
  {?LINE, fun() ->
    Errors = type_system_test:infer_prefix("expr =\n" ++ Expr),
    check_has_errors(Errors),
    Str = lists:flatten(reporter:format(Errors)),
    check(Name, Str)
  end}
).

-define(
  golden_prg_(Name, Prg),
  {?LINE, fun() ->
    Errors = type_system_test:infer_prefix(Prg),
    check_has_errors(Errors),
    Str = lists:flatten(reporter:format(Errors)),
    check(Name, Str)
  end}
).

-define(
  golden_many_(Name, PathPrgs, TargetPath),
  {?LINE, fun() ->
    Dir = utils:temp_dir(),
    Errors = type_system_test:infer_many(Dir, PathPrgs, TargetPath),
    check_has_errors(Errors),

    NormErrors = norm_dir(Errors, Dir),
    Str = lists:flatten(reporter:format(NormErrors)),
    check(Name, Str)
  end}
).

norm_dir([Err | Errs], Dir) -> [norm_dir(Err, Dir) | norm_dir(Errs, Dir)];
norm_dir([], _) -> [];
norm_dir({read_error, Path, Reason}, Dir) ->
  {read_error, replace_dir(Path, Dir), Reason};
norm_dir({import_error, Loc, PathOrCon, Reason, Comp}, Dir) ->
  {import_error, Loc, replace_dir(PathOrCon, Dir), Reason,
   replace_dir(Comp, Dir)};
norm_dir({lexer_errors, Errs, Path, PrgLines}, Dir) ->
  {lexer_errors, Errs, replace_dir(Path, Dir), PrgLines};
norm_dir({parser_errors, Errs, Path, PrgLines}, Dir) ->
  {parser_errors, Errs, replace_dir(Path, Dir), PrgLines};
norm_dir({errors, Errs, Comps}, Dir) ->
  {errors, Errs, [replace_dir(Comp, Dir) || Comp <- Comps]}.

replace_dir(#comp{path=Path}=C, Dir) -> C#comp{path=replace_dir(Path, Dir)};
replace_dir(Path, Dir) -> string:replace(Path, Dir, "dir", all).

check(Name, Str) ->
  {ok, Cwd} = file:get_cwd(),
  Path = filename:join([Cwd, "test", "golden", "reporter-" ++ Name]),

  case init:get_argument(update) of
    {ok, _} ->
      io:format(user, "updated golden file ~p~n", [Name]),
      ?assertEqual(ok, file:write_file(Path, Str));
    error ->
      case file:read_file(Path) of
        {ok, Binary} -> ?assertEqual(unicode:characters_to_list(Binary), Str);
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
  , ?golden_expr_("l-unterminated-raw-string", "`hello\n\nworld\n")
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
        "a = \\something"
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
  , ?golden_expr_("p-bad-map-1", "{ @hello, 3 + 5 }")
  , ?golden_expr_("p-bad-map-2", "{ @hello => 3 + }")
  , ?golden_expr_("p-bad-record", "{ a = 3, b := 4, c := @hi }")
  , ?golden_expr_("p-bad-record-update", "Foo { hey = 'a', hi = true, | foo }")
  , ?golden_expr_("p-bad-tuple-1", "(1,)")
  , ?golden_expr_("p-bad-tuple-2", "('h', -)")
  , ?golden_expr_("p-bad-tuple-te", "(1, @hi) : (Int,)")
  , ?golden_expr_("p-bad-tuple-pattern", "let (1,) = (1, @hi)\n2")
  , ?golden_expr_("p-no-close-1", "{ a = 3")
  , ?golden_expr_("p-no-close-2", "[1, [2, [3, 4], 5, 6]")
  , ?golden_prg_("p-no-open", "enum Bar")
  , ?golden_expr_("p-extra-closing-1", "(match 1 { 1) => 2 })")
  , ?golden_expr_("p-extra-closing-2", "Foo { a = (1 }")
  , ?golden_expr_("p-native-no-atom", "erlang:length([])")
  , ?golden_expr_("p-native-arity", "@erlang:length")
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
  , ?golden_many_("p-no-module", [
      {"foo", "a = 1"}
    ], "foo")
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
        "a = \\14.153.0"
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
  % need to use many here because prg assumes no imports
  , ?golden_many_("import-builtin", [
      {"foo",
        "module Foo\n"
        "import Bar\n"
        "a = 1"
      }
    ], "foo")
  , ?golden_many_("import-self", [
      {"foo",
        "module Foo\n"
        "import \"./foo\"\n"
        "a = 1"
      }
    ], "foo")

  % Ensure comps that have the same name as stdlib modules are retained for
  % error reporting purposes.
  , ?golden_many_("redef-base", [{"base", "module Base"}], "base")
  , ?golden_many_("redef-lexer", [{"lexer", "module Lexer"}], "lexer")
  , ?golden_many_("redef-parser", [{"parser", "module Parser"}], "parser")

  % type system errors
  , ?golden_expr_("ts-mismatch", "true + 5")
  , ?golden_expr_("ts-hole", "true && _")
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
