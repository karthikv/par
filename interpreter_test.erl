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

  , ?_test({3.0, true} = (expr("|x| x"))([{3.0, true}]))
  , ?_test(35.0 = (expr("|x, y| x * y * 3.5"))([4, 2.5]))
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
             expr("let a = [4], f = |x| a ++ x ++ [3] in f([]) ++ f([2])"))

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
  , ?_test({'Bar', true, [<<"hello">>, <<"world">>]} = execute(
      "enum Foo { Bar(Bool, [String]) }\n"
      "main() = Bar(true, [\"hello\", \"world\"])"
    ))
  , ?_test({'Cons', <<"hello">>, {'Cons', {3, true}, 'End'}} = execute(
      "enum VariedList { Cons(A, VariedList), End }\n"
      "main() = Cons(\"hello\", Cons((3, true), End))"
    ))
  , ?_test('Bar' = execute(
      "enum Foo<A> { Bar }\n"
      "main() = Bar"
    ))
  , ?_test({'Other', 3} = execute(
      "enum Foo<A> { Bar, Other(A) }\n"
      "main() = Other(3)"
    ))
  , ?_test({'Cons', 3, {'Cons', 5.0, 'End'}} = execute(
      "enum UniformList<A> { Cons(A, UniformList<A>), End }\n"
      "main() = Cons(3, Cons(5.0, End))\n"
    ))
  ].
