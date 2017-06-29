-module(exec_test).
-export([returns_fun/0]).

-include_lib("eunit/include/eunit.hrl").
-define(TMP_MANY_DIR, "/tmp/exec-test-many").

run_code_gen(Prg) ->
  {ok, _, Comps} = type_system_test:type_check(Prg),
  [{Mod, Binary}] = code_gen:compile_comps(Comps),

  remove(Mod),
  code:load_binary(Mod, "", Binary),

  Mod:'_@init'(gb_sets:new()),
  Mod:main().

run_interpreter(Prg) ->
  {ok, _, [{_, Ast, _, _}]} = type_system_test:type_check(Prg),
  interpreter:run_ast(Ast, []).

expr_code_gen(Expr) -> run_code_gen("main() = " ++ Expr).
expr_interpreter(Expr) -> run_interpreter("main() = " ++ Expr).

many_code_gen(PathPrgs, TargetPath) ->
  {ok, _, Comps} = type_system_test:type_check_many(
    ?TMP_MANY_DIR,
    PathPrgs,
    TargetPath
  ),

  code:add_patha(?TMP_MANY_DIR),
  lists:foreach(fun({Mod, Binary}) ->
    Path = filename:join(?TMP_MANY_DIR, lists:concat([Mod, ".beam"])),
    file:write_file(Path, Binary),
    remove(Mod)
  end, code_gen:compile_comps(Comps)),

  {Module, _, _, _} = hd(Comps),
  Mod = list_to_atom(Module),
  Mod:'_@init'(gb_sets:new()),

  V = Mod:main(),
  code:del_path(?TMP_MANY_DIR),
  V.

remove(Mod) ->
  code:purge(Mod),
  code:delete(Mod),
  code:purge(Mod).

code_gen_expr_test_() -> test_expr(fun expr_code_gen/1).
interpreter_expr_test_() -> test_expr(fun expr_interpreter/1).
test_expr(Expr) ->
  [ ?_test(none = Expr("()"))
  , ?_test(1 = Expr("1"))
  , ?_test(3.0 = Expr("3.0"))
  , ?_test(true = Expr("true"))
  , ?_test($h = Expr("'h'"))
  , ?_test($\n = Expr("'\\n'"))
  , ?_test(<<"hi">> = Expr("\"hi\""))
  , ?_test(<<"hi\n">> = Expr("\"hi\\n\""))
  , ?_test(hi = Expr("@hi"))
  , ?_test('hello world' = Expr("@\"hello world\""))
  , ?_test([3.0, 5] = Expr("[3.0, 5]"))
  , ?_test({<<"what">>, false, 7} = Expr("(\"what\", false, 7)"))
  , ?_assertEqual(#{}, Expr("{}"))
  , ?_assertEqual(
      #{<<"hello">> => <<"world">>, <<"some">> => <<"thing">>},
      Expr("{\"hello\" => \"world\", \"some\" => \"thing\"}")
    )
  , ?_assertEqual(gb_sets:new(), Expr("#[]"))
  , ?_assertEqual(
      gb_sets:from_list([2, 4, 6, 8]),
      Expr("#[2, 4, 2, 6, 4, 8, 6]")
    )


  , ?_test({3.0, true} = (Expr("|x| x"))({3.0, true}))
  , ?_test(35.0 = (Expr("|x, y| x * y * 3.5"))(4, 2.5))
  , ?_test(true = Expr("(|x| x || true)(false)"))
  , ?_test(<<"ab">> = Expr("(|a, b| a ++ b)(\"a\")(\"b\")"))
  , ?_test(5 = Expr("(|x| |y| x + y)(2, 3)"))
  , ?_test([4, 1] = Expr("(|x| |-| x -- [3])([4, 3, 1])()"))
  % to test code_gen_utils:'_@curry' in the parital application case
  , ?_test(2 = Expr(
      "let f = (|a| |b, c, d| a - b + c - d)(4), f = f(3) in f(2, 1)"
    ))


  , ?_test(<<"world">> = Expr("if false then \"hello\" else \"world\""))
  , ?_test([true, false] =
             Expr("if false || true && 3.5 < 4 then [true, false] else [true]"))
  , ?_test(none = Expr("if true then @foo"))
  , ?_test(none = Expr("if false then @io:nl() :: () else discard 3"))
  % ensures that we handle conditions that aren't valid guard clauses
  , ?_test($a = Expr("let f = |x| x == 3 in if f(3) then 'a' else 'b'"))

  , ?_test(5 = Expr("let x = 5 in x"))
  % ensures that we generate a unique name for each variable; otherwise, we'll
  % get a badmatch 4 <=> 5
  , ?_test(5 = Expr("let x = (let x = 4, y = 5 in y) in x"))
  , ?_test(true = Expr("let x = 5, y = true in x == 4 || y"))
  , ?_test(false =
             Expr("let and = |a, b, c| a && b && c in and(true, true, false)"))
  , ?_test([4, 3, 4, 2, 3] =
             Expr("let a = [4], f(x) = a ++ x ++ [3] in f([]) ++ f([2])"))
  , ?_test(15 = Expr("let a = 10, b = a + 5 in b"))
  , ?_test(32 = Expr(
      "let f = |x, c| if x == 0 then c else f(x - 1, c * 2) in\n"
      "  f(5, 1)"
    ))
  , ?_test(true = Expr("let a = 1, a = a == 1 in a"))


  , ?_test(<<"hello">> = Expr("{ \"hello\" }"))
  , ?_test(true = Expr("{ @foo; true }"))
  , ?_assertEqual(
      #{<<"hi">> => 5},
      Expr("let x = 5 in { @erlang:hd([1]); 3.0; {\"hi\" => x} }")
    )

  , ?_test(false = Expr("1 == 2"))
  , ?_test(true = Expr("(3, 4) == (3, 4)"))
  , ?_test(false = Expr("5.0 != 5.0"))
  , ?_test(true = Expr("true != false"))
  , ?_test(true = Expr("false || true"))
  , ?_test(false = Expr("false || false"))
  , ?_test(true = Expr("true && true"))
  , ?_test(false = Expr("false && true"))
  , ?_test(true = Expr("3.0 > 2"))
  , ?_test(false = Expr("5 > 7"))
  , ?_test(true = Expr("1.3 < 1.4"))
  , ?_test(false = Expr("15 < 14"))
  , ?_test(true = Expr("3.0 >= 3.0"))
  , ?_test(false = Expr("2 >= 3"))
  , ?_test(true = Expr("12 <= 12"))
  , ?_test(false = Expr("27 <= 26"))
  , ?_test(3 = Expr("1 + 2"))
  , ?_test(4.2 = Expr("1.5 + 2.7"))
  , ?_test(-3 = Expr("7 - 10"))
  , ?_test(0.5 = Expr("1.5 - 1"))
  , ?_test(854 = Expr("14 * 61"))
  , ?_test(37.12 = Expr("6.4 * 5.8"))
  , ?_test(1.57 = Expr("48.67 / 31"))
  , ?_test(17.0 = Expr("85 / 5"))
  , ?_test(2 = Expr("17 % 3"))
  , ?_test(-3 = Expr("-7 % 4"))
  , ?_test(30.0 = Expr("3 + 5 * 7 - 4 / 2 + 38 % 6 - 8"))
  , ?_test([$a] = Expr("['a' | []]"))
  , ?_test([a, b, c] = Expr("[@a | [@b, @c]]"))
  , ?_test([3, 4, 5] = Expr("[3, 4 | [5]]"))
  , ?_test([[]] = Expr("[[] | []]"))
  , ?_test([1, 2, 3, 4] = Expr("[1] ++ [2, 3, 4]"))
  , ?_test(<<"hello world">> = Expr("\"hello \" ++ \"world\""))
  , ?_assertEqual(
      #{<<"a">> => 1, <<"b">> => 2.0},
      Expr("{\"a\" => 1} ++ {\"b\" => 2.0}")
    )
  , ?_assertEqual(
      gb_sets:from_list([1, 2, 3]),
      Expr("#[1] ++ #[2, 3]")
    )
  , ?_assertEqual(
      [3, 8],
      Expr("[5, 3, 1, 4, 5, 8, 7] -- [4, 1, 5, 7]")
    )
  , ?_assertEqual(
      gb_sets:from_list([3]),
      Expr("#[3, 2, 3, 1, 2] -- #[1, 8, 6, 2]")
    )
  , ?_test(-3 = Expr("-3"))
  , ?_test(-78.5 = Expr("-5 * 15.7"))
  , ?_test(false = Expr("!true"))
  , ?_test(true = Expr("!false && true"))
  , ?_test($h = Expr("$'h'"))


  , ?_test([4, 6] = Expr("@lists:filter(|x| x > 3, [2, 4, 6])"))
  , ?_test([6] = Expr("@lists:filter((|t, x| x > t)(5), [2, 4, 6])"))
  , ?_test([true] = Expr("@lists:map(@erlang:is_atom/1, [@a])"))
  , ?_assertEqual(
      gb_sets:from_list([1, 2, 3]),
      Expr("#[3] ++ let f = @gb_sets:add/2 in f(2)(#[1])")
    )
  , ?_test(3 = Expr("@exec_test:returns_fun()(1)(2)"))
  , ?_test(3 = Expr("@exec_test:returns_fun/0((), 1)(2)"))
  , ?_test(3 = Expr("@exec_test:returns_fun/0((), 1, 2)"))
  , ?_test(true = Expr("let foo(x) = x == () in foo()"))
  , ?_test(true = Expr("let foo(x) = x == () in foo(())"))

  , ?_test(<<"hello world">> = Expr("\"hello\" |> |x| x ++ \" world\""))
  , ?_test(77 = Expr("let inc(x) = x + 1 in (5 |> |x| 2 * x |> inc) * 7"))
  , ?_test(true = (Expr("let f(x, y) = x == y in @hi |> f"))(hi))
  ].

% used for the last few tests above
returns_fun() ->
  fun(A, B) -> A + B end.

code_gen_prg_test_() -> test_prg(fun run_code_gen/1).
interpreter_prg_test_() -> test_prg(fun run_interpreter/1).
test_prg(Run) ->
  [ ?_test(3 = Run(
     "main :: () -> Int\n"
     "main() = 3 :: Int"
    ))
  , ?_test(8 = Run(
      "fib(n) = if n == 0 || n == 1 then n else fib(n - 1) + fib(n - 2)\n"
      "main() = fib(6)"
    ))
  , ?_test([false, false, true] = Run(
      "cmp(f, g, x) = f(g(x))\n"
      "two(e) = [e, e]\n"
      "and_true(l) = l ++ [true]\n"
      "main() = cmp(and_true)(two, false)"
    ))
  , ?_test(50 = Run(
      "f(x) = g(x - 10.0)\n"
      "g(x) = if x >= 0 then 10 + f(x) else 0\n"
      "main() = f(57)"
    ))
  ].

code_gen_global_test_() -> test_global(fun run_code_gen/1).
interpreter_global_test_() -> test_global(fun run_interpreter/1).
test_global(Run) ->
  [ ?_test(3 = Run(
      "foo = 3\n"
      "main() = foo"
    ))
  , ?_test([false, true] = Run(
      "foo = baz && false\n"
      "bar = [foo] ++ [true]\n"
      "baz = true\n"
      "main() = bar"
    ))
  , ?_test(7812.5 = Run(
      "foo = |x| bar(x) / 2\n"
      "bar(x) = if x == 0 then 1 else foo(x - 1) * 10\n"
      "main() = foo(6)"
    ))
  % to ensure no warnings from arg shadowing b/c of currying
  , ?_test({{<<"hi">>, $d}, 3, 4} = Run(
      "bar(a, b, c) = (a('d'), b, c)\n"
      "baz(a, b) = (a, b)\n"
      "foo = bar(baz(\"hi\"))\n"
      "main() = foo(3, 4)"
    ))
  % to ensure globals are evaluated strictly in order
  , ?_test("hi" = Run(
      "foo = to_list(\"hi\")\n"
      "to_list = @erlang:binary_to_list/1\n"
      "main() = foo"
    ))
  % to ensure globals are only evaluated once
  , ?_test({ok, <<"bar">>} = Run(
      "foo = @file:write_file(\"/tmp/par-foo\", \"bar\")\n"
      "bar = let result = @file:read_file(\"/tmp/par-foo\") in\n"
      "  { @file:delete(\"/tmp/par-foo\"); result }"
      "main() = bar"
    ))
  % to ensure indirect global dependencies (foo -> f -> b) work
  , ?_test(8 = Run(
      "foo = f(3)\n"
      "f(x) = x + bar\n"
      "bar = 5\n"
      "main() = foo"
    ))
  ].

code_gen_enum_test_() -> test_enum(fun run_code_gen/1).
interpreter_enum_test_() -> test_enum(fun run_interpreter/1).
test_enum(Run) ->
  [ ?_test('Bar' = Run(
      "enum Foo { Bar }\n"
      "main() = Bar"
    ))
  , ?_test({'Other', 5} = Run(
      "enum Foo { Bar, Other(Int) }\n"
      "main() = Other(5)"
    ))
  , ?_test({'Bar', true, [<<"hello">>]} = (Run(
      "enum Foo { Bar(Bool, [String]) }\n"
      "main() = Bar(true)"
    ))([<<"hello">>]))
  , ?_test('Bar' = Run(
      "enum Foo<A> { Bar }\n"
      "main() = Bar"
    ))
  , ?_test({'Other', 3} = Run(
      "enum Foo<A> { Bar, Other(A) }\n"
      "main() = Other(3)"
    ))
  , ?_test({'Cons', 3, {'Cons', 5.0, 'End'}} = Run(
      "enum CustomList<A> { Cons(A, CustomList<A>), End }\n"
      "main() = Cons(3, Cons(5.0, End))\n"
    ))
  , ?_test(error = Run(
      "enum Result { Err @error }\n"
      "main() = Err"
    ))
  , ?_test({ok, 5} = Run(
      "enum Result<T> { Ok(T) @ok }\n"
      "main() = Ok(5)"
    ))
  , ?_test({'==', true, <<"hi">>} = Run(
      "enum Expr { Eq(Bool, String) @\"==\" }\n"
      "main() = Eq(true, \"hi\")"
    ))
  ].

code_gen_record_test_() ->
  test_record(fun expr_code_gen/1, fun run_code_gen/1).
interpreter_record_test_() ->
  test_record(fun expr_interpreter/1, fun run_interpreter/1).
test_record(Expr, Run) ->
  [ ?_assertEqual(#{bar => 3}, Expr("{ bar = 3 }"))
  , ?_assertEqual(#{bar => 3, baz => true}, Expr("{ bar = 3, baz = true }"))
  , ?_test(8 = Expr("{ bar = |x| x + 5 }.bar(3)"))
  , ?_assertEqual(#{bar => 4.0}, Expr("{ { bar = 3 } | bar = 4.0 }"))

  , ?_test(false = Expr("{ bar = 3 } == { bar = 5 }"))
  , ?_test(true = Expr("{ bar = 3 } == { bar = 3 }"))


  , ?_test(true = Expr("let f(x) = x.bar || false in f({ bar = true })"))
  , ?_test(hi = Expr("let f(x) = x.bar in f({ bar = @hi, baz = 7 })"))

  , ?_test({11, <<"oh, hi">>} = Run(
      "f(x) = (x.bar + 4, x.foo ++ \"hi\")\n"
      "main() = f({ bar = 7, foo = \"oh, \" })"
    ))

  % named struct
  , ?_assertEqual(#{bar => 3}, Run(
      "struct Foo { bar :: Int }\n"
      "main() = Foo(3)"
    ))
  , ?_assertEqual(#{bar => 3}, Run(
      "struct Foo { bar :: Int }\n"
      "main() = Foo { bar = 3 }"
    ))
  , ?_assertEqual(#{bar => 3, baz => [<<"hello">>]}, (Run(
      "struct Foo { bar :: Int, baz :: [String] }\n"
      "main() = Foo(3)"
    ))([<<"hello">>]))
  , ?_assertEqual(#{baz => [first, second], bar => 15}, Run(
      "struct Foo { bar :: Int, baz :: [Atom] }\n"
      "main() = Foo { baz = [@first, @second], bar = 15 }"
    ))
  , ?_assertEqual(#{bar => hi, baz => true}, (Run(
      "struct Foo<X, Y> { bar :: X, baz :: Y }\n"
      "main() = Foo(@hi)"
    ))(true))
  , ?_assertEqual(#{bar => hi}, Run(
      "struct Foo<X> { bar :: X }\n"
      "main() = Foo { bar = @hi }"
    ))
  % Won't be able to create a valid Foo, but should still type check.
  , ?_test(true = Run(
      "struct Foo { baz :: Foo }\n"
      "main() = true"
    ))
  , ?_assertEqual(#{bar => hi, baz => [#{bar => hello, baz => []}]}, Run(
      "struct Foo { bar :: Atom, baz :: [Foo] }\n"
      "main() = Foo { bar = @hi, baz = [Foo { bar = @hello, baz = [] }] }"
    ))


  % generalization cases
  , ?_test({<<"hi">>, true} = Run(
      "struct Foo<A> { bar :: A }\n"
      "main() = let id(a) = a, f = Foo { bar = id } in\n"
      "  (f.bar(\"hi\"), f.bar(true))"
    ))
  , ?_test(7.5 = Run(
      "f(x, y) = x.foo(y.bar)\n"
      "main() = f({ foo = |x| x.baz }, { bar = { baz = 7.5 } })"
    ))
  ].

code_gen_pattern_test_() ->
  test_pattern(fun expr_code_gen/1, fun run_code_gen/1).
interpreter_pattern_test_() ->
  test_pattern(fun expr_interpreter/1, fun run_interpreter/1).
test_pattern(Expr, Run) ->
  [ ?_test(true = Expr("match 3 { 3 => true, 4 => false }"))
  , ?_test(18 = Expr("let x = 3 in match x + 5 { a => a + 10 }"))
  , ?_test(hello = Expr("match 'x' { 'y' => @hi, 'x' => @hello }"))
  , ?_test(5.0 = Expr("match |x| x { id => let y = id(true) in id(5.0) }"))
  , ?_test({6, 6.0, 8, 8.0} = Expr(
      "match (3, 4) {\n"
      "  (a, b) => (a + 3 :: Int, a + 3.0, b + 4 :: Int, b + 4.0)\n"
      "}"
    ))
  , ?_test(5 = Run(
      "enum Foo { Bar, Baz(Int) }\n"
      "main() = match Baz(5) { Bar => 1, Baz(x) => x }"
    ))
  , ?_test(-3 = Run(
      "enum Foo { Bar @a, Baz(Int) @hi }\n"
      "main() = match (Bar) { Bar => 1, Baz(_) => 2 } +\n"
      "  match Baz(4) { Bar => -3, Baz(x) => -x }"
    ))
  , ?_test([<<"hey">>] = Expr(
      "match [\"hi\", \"hey\"] { [] => [], [s] => [s], [_ | t] => t }"
    ))
  , ?_test(2.0 = Expr(
      "let x = [([], \"hi\", 3.0), ([2, 3], \"hey\", 58.0)] in"
      "  match x {\n"
      "    [([h | t], _, _) | _] => h,\n"
      "    [_, ([], _, c)] => c,\n"
      "    [(_, _, c), ([x, y | []], _, _)] => c + x - y\n"
      "  }"
    ))
  , ?_test([1, 2] = Expr(
      "let x = 3, y = [2] in match [1] { *y => y ++ [1], x => x ++ [2] }"
    ))


  , ?_test([] = Expr("let 3 = 3 in []"))
  , ?_test({5, 5.0} = Expr(
      "let [_, (x, _, _)] = [(1, \"foo\", @foo), (2, \"bar\", @bar)] in\n"
      "  (x + 3 :: Int, x + 3.0)"
    ))
  , ?_test(7 = Expr("let [_, a] = [1, 3], (*a, b, *a) = (3, 7, 3) in b"))


  , ?_test(none = Expr("if let a = 3.0 then a"))
  % to ensure env is reset appropriately
  , ?_test(true = Expr("let a = true in { if let a = 3.0 then a; a }"))
  , ?_test(true = Expr("let a = true in { if let a = 3.0 then a else 5; a }"))
  , ?_test(3 = Expr(
      "if let abs(x) = if x < 0 then abs(-x) else x then abs(-3) else 0"
    ))
  , ?_test(<<"hey">> = Expr("if let (2, a) = (1, \"hi\") then a else \"hey\""))
  , ?_test(2.5 = Expr(
      "if let f = |b| if b then f(!b) + 1 else 1.5\n"
      "then f(true)\n"
      "else 0"
    ))
  ].

code_gen_import_test_() -> test_import(fun many_code_gen/2).
% TODO: defer interpreter import until we work on REPL
test_import(Many) ->
  [ ?_test(7 = Many([
      {"foo", "module Foo export x = 3"},
      {"bar", "module Bar import \"./foo\" main() = Foo.x + 4"}
    ], "bar"))
  , ?_test(7 = Many([
      {"foo", "module Foo export x = 3"},
      {"bar", "module Bar import \"./foo.par\" main() = Foo.x + 4"}
    ], "bar"))
  , ?_test(<<"hi">> = Many([
      {"foo", "module Foo x = 3"},
      {"bar", "module Bar import \"./foo\" main() = \"hi\""}
    ], "bar"))
  , ?_test(true = Many([
      {"foo", "module Foo export x = 3.0"},
      {"a/bar", "module Bar import \"../foo\" export x = Foo.x == 3.0"},
      {"b/baz", "module Baz import \"../a/bar\" main() = Bar.x || false"}
    ], "b/baz"))
  , ?_test([a, b, b] = Many([
      {"foo", "module Foo export x = [@a] export twice(x) = [x, x]"},
      {"a/bar",
        "module Bar\n"
        "import \"../foo\"\n"
        "import \"../b/baz\"\n"
        "main() = Foo.x ++ Baz.z"},
      {"b/baz",
        "module Baz\n"
        "import \"../foo\"\n"
        "export z = Foo.twice(@b)"}
    ], "a/bar"))
  , ?_test(100 = Many([
      {"foo",
        "module Foo\n"
        "import \"./bar\"\n"
        "export f(x) = Bar.g(x - 10.0)\n"
        "main() = f(27)"},
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "export g(x) = if x >= 0 then 10 * Foo.f(x) else 1"}
    ], "foo"))
  , ?_test({'BazInt', 3} = Many([
      {"foo", "module Foo enum Baz { BazInt(Int) }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "x :: Foo.Baz\n"
        "x = Foo.BazInt(3)\n"
        "main() = x"}
    ], "bar"))
  , ?_assertEqual(
      #{a => 3},
      Many([
        {"foo", "module Foo struct Baz { a :: Int }"},
        {"bar",
          "module Bar\n"
          "import \"./foo\"\n"
          "x :: Foo.Baz\n"
          "x = Foo.Baz(3)\n"
          "main() = x"}
      ], "bar")
    )
  , ?_test({'Foo', 3} = Many([
      {"foo", "module Foo enum Foo { Foo(Int) }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "x :: Foo.Foo\n"
        "x = Foo.Foo(3)\n"
        "main() = x"}
    ], "bar"))
  , ?_test(7 = Many([
      {"foo", "module Foo enum Foo { Foo(Int) }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "x = match Foo.Foo(7) { Foo.Foo(n) => n }\n"
        "main() = x"}
    ], "bar"))
  , ?_assertEqual(
      {'Baz', #{a => 3}},
      Many([
        {"foo", "module Foo struct Baz { a :: Int }"},
        {"bar",
          "module Bar\n"
          "import \"./foo\"\n"
          "enum Baz { Baz(Foo.Baz) }\n"
          "x :: Baz\n"
          "x = Baz(Foo.Baz(3))\n"
          "main() = x"}
      ], "bar")
    )
  , ?_test(4 = Many([
      {"foo",
        "module Foo\n"
        "import \"./bar\"\n"
        "export a = Bar.b\n"
        "export c(x) = x + 1\n"
        "main() = a"},
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "export b = Foo.c(3)"}
    ], "foo"))
  ].
