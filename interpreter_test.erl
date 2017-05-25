-module(interpreter_test).
-export([run/0, returns_fun/0]).
-include_lib("eunit/include/eunit.hrl").

run() ->
  interpreter:reload(false),

  code:soft_purge(?MODULE),
  {ok, _} = compile:file(?MODULE),
  code:load_file(?MODULE),

  ?MODULE:test().

execute(Prg) ->
  {ok, _, Ast} = par:infer_prg(Prg),
  interpreter:execute(Ast).

expr(Expr) ->
  execute("main() = " ++ Expr).

expr_test_() ->
  [ ?_test(none = expr("()"))
  , ?_test(1 = expr("1"))
  , ?_test(3.0 = expr("3.0"))
  , ?_test(true = expr("true"))
  , ?_test(<<"hi">> = expr("\"hi\""))
  , ?_test(hi = expr("@hi"))
  , ?_test('hello world' = expr("@\"hello world\""))
  , ?_test([3.0, 5] = expr("[3.0, 5]"))
  , ?_test({<<"what">>, false} = expr("(\"what\", false)"))
  , ?_assertEqual(#{}, expr("{}"))
  , ?_assertEqual(
      #{<<"hello">> => <<"world">>, <<"some">> => <<"thing">>},
      expr("{\"hello\" => \"world\", \"some\" => \"thing\"}")
    )
  , ?_assertEqual(gb_sets:new(), expr("#[]"))
  , ?_assertEqual(
      gb_sets:from_list([2, 4, 6, 8]),
      expr("#[2, 4, 2, 6, 4, 8, 6]")
    )


  , ?_test({3.0, true} = (expr("|x| x"))({3.0, true}))
  , ?_test(35.0 = (expr("|x, y| x * y * 3.5"))(4, 2.5))
  , ?_test(true = expr("(|x| x || true)(false)"))
  , ?_test(<<"ab">> = expr("(|a, b| a ++ b)(\"a\")(\"b\")"))
  , ?_test(5 = expr("(|x| |y| x + y)(2, 3)"))
  , ?_test([4, 1] = expr("(|x| |-| x -- [3])([4, 3, 1])()"))


  , ?_test(<<"world">> = expr("if false then \"hello\" else \"world\""))
  , ?_test([true, false] =
             expr("if false || true && 3.5 < 4 then [true, false] else [true]"))
  , ?_test(none = expr("if true then @foo"))
  , ?_test(none = expr("if false then @io:nl() :: () else discard 3"))

  , ?_test(5 = expr("let x = 5 in x"))
  , ?_test(true = expr("let x = 5, y = true in x == 4 || y"))
  , ?_test(false =
             expr("let and = |a, b, c| a && b && c in and(true, true, false)"))
  , ?_test([4, 3, 4, 2, 3] =
             expr("let a = [4], f(x) = a ++ x ++ [3] in f([]) ++ f([2])"))
  , ?_test(15 = expr("let a = b + 5, b = 10 in a"))
  , ?_test(32 = expr(
      "let f = |x, c| if x == 0 then c else f(x - 1, c * 2) in\n"
      "  f(5, 1)"
    ))


  , ?_test(<<"hello">> = expr("{ \"hello\" }"))
  , ?_test(true = expr("{ @foo; true }"))
  , ?_assertEqual(
      #{<<"hi">> => 5},
      expr("let x = 5 in { @erlang:hd([1]); 3.0; {\"hi\" => x} }")
    )

  , ?_test(false = expr("1 == 2"))
  , ?_test(true = expr("(3, 4) == (3, 4)"))
  , ?_test(false = expr("5.0 != 5.0"))
  , ?_test(true = expr("true != false"))
  , ?_test(true = expr("false || true"))
  , ?_test(false = expr("false || false"))
  , ?_test(true = expr("true && true"))
  , ?_test(false = expr("false && true"))
  , ?_test(true = expr("3.0 > 2"))
  , ?_test(false = expr("5 > 7"))
  , ?_test(true = expr("1.3 < 1.4"))
  , ?_test(false = expr("15 < 14"))
  , ?_test(true = expr("3.0 >= 3.0"))
  , ?_test(false = expr("2 >= 3"))
  , ?_test(true = expr("12 <= 12"))
  , ?_test(false = expr("27 <= 26"))
  , ?_test(3 = expr("1 + 2"))
  , ?_test(4.2 = expr("1.5 + 2.7"))
  , ?_test(-3 = expr("7 - 10"))
  , ?_test(0.5 = expr("1.5 - 1"))
  , ?_test(854 = expr("14 * 61"))
  , ?_test(37.12 = expr("6.4 * 5.8"))
  , ?_test(1.57 = expr("48.67 / 31"))
  , ?_test(17.0 = expr("85 / 5"))
  , ?_test(2 = expr("17 % 3"))
  , ?_test(-3 = expr("-7 % 4"))
  , ?_test(30.0 = expr("3 + 5 * 7 - 4 / 2 + 38 % 6 - 8"))
  , ?_test([1, 2, 3, 4] = expr("[1] ++ [2, 3, 4]"))
  , ?_test(<<"hello world">> = expr("\"hello \" ++ \"world\""))
  , ?_assertEqual(
      #{<<"a">> => 1, <<"b">> => 2.0},
      expr("{\"a\" => 1} ++ {\"b\" => 2.0}")
    )
  , ?_assertEqual(
      gb_sets:from_list([1, 2, 3]),
      expr("#[1] ++ #[2, 3]")
    )
  , ?_assertEqual(
      [3, 8],
      expr("[5, 3, 1, 4, 5, 8, 7] -- [4, 1, 5, 7]")
    )
  , ?_assertEqual(
      gb_sets:from_list([3]),
      expr("#[3, 2, 3, 1, 2] -- #[1, 8, 6, 2]")
    )
  , ?_test(-3 = expr("-3"))
  , ?_test(-78.5 = expr("-5 * 15.7"))
  , ?_test(false = expr("!true"))
  , ?_test(true = expr("!false && true"))


  , ?_test([4, 6] = expr("@lists:filter(|x| x > 3, [2, 4, 6])"))
  , ?_test([6] = expr("@lists:filter((|t, x| x > t)(5), [2, 4, 6])"))
  , ?_test([true] = expr("@lists:map(@erlang:is_atom/1, [@a])"))
  , ?_assertEqual(
      gb_sets:from_list([1, 2, 3]),
      expr("#[3] ++ let f = @gb_sets:add/2 in f(2)(#[1])")
    )
  , ?_test(3 = expr("@interpreter_test:returns_fun()(1)(2)"))
  , ?_test(3 = expr("@interpreter_test:returns_fun/0((), 1)(2)"))
  , ?_test(3 = expr("@interpreter_test:returns_fun/0((), 1, 2)"))
  , ?_test(true = expr("let foo(x) = x == () in foo()"))
  , ?_test(true = expr("let foo(x) = x == () in foo(())"))
  ].

% used for the last few tests above
returns_fun() ->
  fun(A, B) -> A + B end.

prg_test_() ->
  [ ?_test(3 = execute(
     "main :: () -> Int\n"
     "main() = 3 :: Int"
    ))
  , ?_test(6765 = execute(
      "fib(n) = if n == 0 || n == 1 then n else fib(n - 1) + fib(n - 2)\n"
      "main() = fib(20)"
    ))
  , ?_test([false, false, true] = execute(
      "cmp(f, g, x) = f(g(x))\n"
      "two(e) = [e, e]\n"
      "and_true(l) = l ++ [true]\n"
      "main() = cmp(and_true)(two, false)"
    ))
  , ?_test(50 = execute(
      "f(x) = g(x - 10.0)\n"
      "g(x) = if x >= 0 then 10 + f(x) else 0\n"
      "main() = f(57)"
    ))
  ].

global_test_() ->
  [ ?_test(3 = execute(
      "foo = 3\n"
      "main() = foo"
    ))
  , ?_test([false, true] = execute(
      "foo = baz && false\n"
      "bar = [foo] ++ [true]\n"
      "baz = true\n"
      "main() = bar"
    ))
  , ?_test(7812.5 = execute(
      "foo = |x| bar(x) / 2\n"
      "bar(x) = if x == 0 then 1 else foo(x - 1) * 10\n"
      "main() = foo(6)"
    ))


  % to ensure globals are evaluated strictly in order
  , ?_test({ok, <<"bar">>} = execute(
      "foo = @file:write_file(\"/tmp/par-foo\", \"bar\")\n"
      "main() = let result = @file:read_file(\"/tmp/par-foo\") in\n"
      "  { @file:delete(\"/tmp/par-foo\"); result }"
    ))
  ].

enum_test_() ->
  [ ?_test('Bar' = execute(
      "enum Foo { Bar }\n"
      "main() = Bar"
    ))
  , ?_test({'Other', 5} = execute(
      "enum Foo { Bar, Other(Int) }\n"
      "main() = Other(5)"
    ))
  , ?_test({'Bar', true, [<<"hello">>]} = (execute(
      "enum Foo { Bar(Bool, [String]) }\n"
      "main() = Bar(true)"
    ))([<<"hello">>]))
  , ?_test('Bar' = execute(
      "enum Foo<A> { Bar }\n"
      "main() = Bar"
    ))
  , ?_test({'Other', 3} = execute(
      "enum Foo<A> { Bar, Other(A) }\n"
      "main() = Other(3)"
    ))
  , ?_test({'Cons', 3, {'Cons', 5.0, 'End'}} = execute(
      "enum CustomList<A> { Cons(A, CustomList<A>), End }\n"
      "main() = Cons(3, Cons(5.0, End))\n"
    ))
  ].

record_test_() ->
  [ ?_assertEqual(#{bar => 3}, expr("{ bar = 3 }"))
  , ?_assertEqual(#{bar => 3, baz => true}, expr("{ bar = 3, baz = true }"))
  , ?_test(8 = expr("{ bar = |x| x + 5 }.bar(3)"))
  , ?_assertEqual(#{bar => 4.0}, expr("{ { bar = 3 } | bar = 4.0 }"))

  , ?_test(false = expr("{ bar = 3 } == { bar = 5 }"))
  , ?_test(true = expr("{ bar = 3 } == { bar = 3 }"))


  , ?_test(true = expr("let f(x) = x.bar || false in f({ bar = true })"))
  , ?_test(hi = expr("let f(x) = x.bar in f({ bar = @hi, baz = 7 })"))

  , ?_test({11, <<"oh, hi">>} = execute(
      "f(x) = (x.bar + 4, x.foo ++ \"hi\")\n"
      "main() = f({ bar = 7, foo = \"oh, \" })"
    ))

  % named struct
  , ?_assertEqual(#{bar => 3}, execute(
      "struct Foo { bar :: Int }\n"
      "main() = Foo(3)"
    ))
  , ?_assertEqual(#{bar => 3}, execute(
      "struct Foo { bar :: Int }\n"
      "main() = Foo { bar = 3 }"
    ))
  , ?_assertEqual(#{bar => 3, baz => [<<"hello">>]}, (execute(
      "struct Foo { bar :: Int, baz :: [String] }\n"
      "main() = Foo(3)"
    ))([<<"hello">>]))
  , ?_assertEqual(#{baz => [first, second], bar => 15}, execute(
      "struct Foo { bar :: Int, baz :: [Atom] }\n"
      "main() = Foo { baz = [@first, @second], bar = 15 }"
    ))
  , ?_assertEqual(#{bar => hi, baz => true}, (execute(
      "struct Foo<X, Y> { bar :: X, baz :: Y }\n"
      "main() = Foo(@hi)"
    ))(true))
  , ?_assertEqual(#{bar => hi}, execute(
      "struct Foo<X> { bar :: X }\n"
      "main() = Foo { bar = @hi }"
    ))
  % Won't be able to create a valid Foo, but should still type check.
  , ?_test(true = execute(
      "struct Foo { baz :: Foo }\n"
      "main() = true"
    ))
  , ?_assertEqual(#{bar => hi, baz => [#{bar => hello, baz => []}]}, execute(
      "struct Foo { bar :: Atom, baz :: [Foo] }\n"
      "main() = Foo { bar = @hi, baz = [Foo { bar = @hello, baz = [] }] }"
    ))


  % generalization cases
  , ?_test({<<"hi">>, true} = execute(
      "struct Foo<A> { bar :: A }\n"
      "main() = let id(a) = a, f = Foo { bar = id } in\n"
      "  (f.bar(\"hi\"), f.bar(true))"
    ))
  , ?_test(7.5 = execute(
      "f(x, y) = x.foo(y.bar)\n"
      "main() = f({ foo = |x| x.baz }, { bar = { baz = 7.5 } })"
    ))
  ].

pattern_test_() ->
  [ ?_test(true = expr("match 3 { 3 => true, 4 => false }"))
  , ?_test(18 = expr("let x = 3 in match x + 5 { a => a + 10 }"))
  , ?_test(5.0 = expr("match |x| x { id => let y = id(true) in id(5.0) }"))
  , ?_test({6, {6.0, {8, 8.0}}} = expr(
      "match (3, 4) {\n"
      "  (a, b) => (a + 3 :: Int, a + 3.0, b + 4 :: Int, b + 4.0)\n"
      "}"
    ))
  , ?_test(5 = execute(
      "enum Foo { Bar, Baz(Int) }\n"
      "main() = match Baz(5) { Bar => 1, Baz(x) => x }"
    ))
  , ?_test([<<"hey">>] = expr(
      "match [\"hi\", \"hey\"] { [] => [], [s] => [s], [_ | t] => t }"
    ))
  , ?_test({{false, hi}, 3} = expr(
      "match (1, true, @hi) {\n"
      "  (0, b) => (b, 10),\n"
      "  (a, true, c) => ((false, c), 3 * a),\n"
      "  (a, b) => (b, a / 2)\n"
      "}"
    ))
  , ?_test(2.0 = expr(
      "let x = [([], \"hi\", 3.0), ([2, 3], \"hey\", 58.0)] in"
      "  match x {\n"
      "    [([h | t], _) | _] => h,\n"
      "    [_, ([], _, c)] => c,\n"
      "    [(_, _, c), ([x, y | []], _)] => c + x - y\n"
      "  }"
    ))
  , ?_test([1, 2] = expr(
      "let x = 3, y = [2] in match [1] { *y => y ++ [1], x => x ++ [2] }"
    ))


  , ?_test([] = expr("let 3 = 3 in []"))
  , ?_test({5, 5.0} = expr(
      "let [_, (x, _)] = [(1, \"foo\", @foo), (2, \"bar\", @bar)] in\n"
      "  (x + 3 :: Int, x + 3.0)"
    ))
  , ?_test(7 = expr("let (*a, b, *a) = (3, 7, 3), [_, a] = [1, 3] in b"))


  , ?_test(none = expr("if let a = 3.0 then a"))
  , ?_test(3 = expr(
      "if let abs(x) = if x < 0 then abs(-x) else x then abs(-3) else 0"
    ))
  , ?_test(<<"hey">> = expr("if let (2, a) = (1, \"hi\") then a else \"hey\""))
  , ?_test(2.5 = expr(
      "if let [f] = [|b| if b then f(!b) + 1 else 1.5]\n"
      "then f(true)\n"
      "else 0"
    ))
  ].
