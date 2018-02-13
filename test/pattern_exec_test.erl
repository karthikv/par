-module(pattern_exec_test).
-include_lib("eunit/include/eunit.hrl").

code_gen_pattern_test_() ->
  test_pattern(
    fun exec_test:expr_code_gen/1,
    fun exec_test:run_code_gen/1
  ).
interpreter_pattern_test_() ->
  test_pattern(
    fun exec_test:expr_interpreter/1,
    fun exec_test:run_interpreter/1
  ).
test_pattern(Expr, Run) ->
  [ ?_test(true = Expr("match 3 { 3 => true, 4 => false, _ => false }"))
  , ?_test(false = Expr("match -4.8 { -3 => true, -4.8 => false, _ => true }"))
  , ?_test(18 = Expr(
      "let x = 3\n"
      "match x + 5 { a => a + 10 }"
    ))
  , ?_test(hello = Expr("match 'x' { 'y' => @hi, 'x' => @hello, _ => @hey }"))
  , ?_test(5.0 = Expr(
      "match |x| x {\n"
      "  id =>\n"
      "    let y = id(true)\n"
      "    id(5.0)\n"
      "}"
    ))
  , ?_test({} = Expr("match () { () => () }"))
  , ?_test({6, 6.0, 8, 8.0} = Expr(
      "match (3, 4) {\n"
      "  (a, b) => (a + 3 : Int, a + 3.0, b + 4 : Int, b + 4.0)\n"
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
      "let x = [([], \"hi\", 3.0), ([2, 3], \"hey\", 58.0)]\n"
      "match x {\n"
      "  [([h | t], _, _) | _] => h\n"
      "  [_, ([], _, c)] => c\n"
      "  [(_, _, c), ([x, y | []], _, _)] => c + x - y\n"
      "  _ => 0\n"
      "}"
    ))
  , ?_test([1, 1] = Expr(
      "let (x, y) = (3, @hey)\n"
      "match [1] { y => y ++ [1], x => x ++ [2] }"
    ))
  , ?_test($h = Expr("(|(a, _)| a)(('h', true))"))
  , ?_test(2 = Run(
      "f(3, [x | _]) = 3 + x\n"
      "main() = f(3, [-1])"
    ))
  , ?_assertError(function_clause, Run(
      "f(3, [x | _]) = 3 + x\n"
      "main() = f(4, [-1])"
    ))
  , ?_test({true, hey} = Run(
      "enum Foo<A> { Bar(Atom), Baz(A) }\n"
      "f(Bar(x), [Baz(y), Baz(z) | _]) = (x == z, y)\n"
      "main() = f(Bar(@hi), [Baz(@hey), Baz(@hi), Baz(@hello)])"
    ))
  , ?_assertError(function_clause, Run(
      "enum Foo<A> { Bar(Atom), Baz(A) }\n"
      "f(Bar(x), [Baz(y), Baz(z) | _]) = y\n"
      "main() = f(Bar(@hi), [Baz(@hey)])"
    ))


  , ?_test([] = Expr(
      "let 3 = 3\n"
      "[]"
    ))
  , ?_test({5, 5.0} = Expr(
      "let [_, (x, _, _)] = [(1, \"foo\", @foo), (2, \"bar\", @bar)]\n"
      "(x + 3 : Int, x + 3.0)"
    ))


  , ?_test({} = Expr("if let a = 3.0 then a"))
  % To ensure env is reset appropriately.
  , ?_test(true = Expr(
      "let a = true\n"
      "if let a = 3.0 then a\n"
      "a"
    ))
  , ?_test(true = Expr(
      "let a = true\n"
      "if let a = 3.0 then a else 5\n"
      "a"
    ))
  % Ensure the correct a is used in the else clause. The Erlang compiler
  % will complain if a is unbound.
  , ?_test(3 = Expr("(|a| if let a = a + 1 then a else a)(2)"))
  , ?_test(<<"hey">> = Expr("if let (2, a) = (1, \"hi\") then a else \"hey\""))
  , ?_test(2.5 = Expr(
      "if let f = |b| if b then f(!b) + 1 else 1.5\n"
      "then f(true)\n"
      "else 0"
    ))
  ].
