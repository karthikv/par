-module(pattern_test).
-import(type_system_test, [
  ok_expr/1,
  bad_expr/2,
  ok_prg/2,
  bad_prg/2,
  l/2,
  l/3,
  l/4
]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/common.hrl").

patterns_test_() ->
  [ ?_test("Bool" = ok_expr("match 3 { 3 => true, 4.8 => false, _ => false }"))
  , ?_test("Bool" = ok_expr(
      "match -4.8 { -3 => true, -4.8 => false, _ => true }"
    ))
  , ?_test("A ~ Num" = ok_expr(
      "let x = 3\n"
      "match x + 5 { a => a + 10 }"
    ))
  , ?_test("Atom" = ok_expr(
      "match 'x' { 'y' => @hi, 'x' => @hello, _ => @hey }"
    ))
  , ?_test("Float" = ok_expr(
      "match |x| x {\n"
      "  id =>\n"
      "    let y = id(true)\n"
      "    id(5.0)\n"
      "}"
    ))
  , ?_test("()" = ok_expr("match () { () => () }"))
  , ?_test("(Int, Float, Int, Float)" = ok_expr(
      "match (3, 4) {\n"
      "  (a, b) => (a + 3 : Int, a + 3.0, b + 4 : Int, b + 4.0)\n"
      "}"
    ))
  , ?_test("Foo -> A ~ Num" = ok_prg(
      "enum Foo { One, Two(Bool), Three }\n"
      "f(x) = match x { One => 1, Two(_) => 2, Three => 3 }",
      "f"
    ))
  , ?_test("Int" = ok_prg(
      "enum Foo { Bar, Baz(Int) }\n"
      "expr = match Baz(5) { Bar => 1, Baz(x) => x }",
      "expr"
    ))
  , ?_test("Int" = ok_prg(
      "enum Foo { Bar, Baz(Int) }\n"
      "expr = match Baz(5) { Mod.Bar => 1, Mod.Baz(x) => x }",
      "expr"
    ))
  , ?_test("[String]" = ok_expr(
      "match [\"hi\", \"hey\"] { [] => [], [s] => [s], [_ | t] => t }"
    ))
  , ?_test("A ~ Num" = ok_expr(
      "match @io:printable_range() {\n"
      "  (a, _) => 1\n"
      "  [] => 2\n"
      "  @error => 3\n"
      "  _ => 4\n"
      "}"
    ))
  , ?_test("Float" = ok_expr(
      "let m = [([], \"hi\", 3.0), ([2, 3], \"hey\", 58.0)]\n"
      "match m {\n"
      "  [([h | t], _, _) | _] => h\n"
      "  [_, ([], _, c)] => c\n"
      "  [(_, _, c), ([x, y | []], _, _)] => c + x - y\n"
      "  _ => 0\n"
      "}"
    ))
  , ?_test("[A ~ Num]" = ok_expr(
      "let (x, y) = (3, @hey)\n"
      "match [1] { y => y ++ [1], x => x ++ [2] }"
    ))
  , ?_test("((A, B)) -> A" = ok_expr("|(a, _)| a"))
  , ?_test("(A ~ Num, [B ~ Num]) -> B ~ Num" = ok_prg(
      "f(3, [x | _]) = 3 + x",
      "f"
    ))
  , ?_test("(Foo<A>, [Foo<Atom>]) -> (Bool, Atom)" = ok_prg(
      "enum Foo<A> { Bar(Atom), Baz(A) }\n"
      "f(Bar(x), [Baz(y), Baz(z) | _]) = (x == z, y)",
      "f"
    ))
  , ?_test(bad_expr(
      "match \"hi\" { \"hey\" => true, \"hello\" => 1 }",
      {"Bool", "A ~ Num", l(39, 1), ?FROM_MATCH_BODY}
    ))
  , ?_test(bad_expr(
      "match \"hi\" { @hi => [1, 2], \"hello\" => [3.0, 7, 5] }",
      {"String", "Atom", l(13, 3), ?FROM_MATCH_PATTERN}
    ))
  , ?_test(bad_prg(
      "enum Foo { Bar, Baz(Int) }\n"
      "enum Animal { Cat, Dog }\n"
      "expr = match Baz(5) { Cat => 3, Bar => 1 }",
      {"Foo", "Animal", l(2, 22, 3), ?FROM_MATCH_PATTERN}
    ))
  , ?_test(bad_expr(
      "match [1, 2] { [a, b] => a + b, [_ | t] => t }",
      {"[A ~ Num]", "B ~ Num", l(43, 1), ?FROM_MATCH_BODY}
    ))
  , ?_test(bad_expr(
      "match (1, true, @hi) {\n"
      "  (0, b, c) => (b, 10)\n"
      "  (a, b, c, d) => (b, a / 2)\n"
      "}",
      {"(A ~ Num, Bool, Atom)", "(B, C, D, E)", l(2, 2, 12),
       ?FROM_MATCH_PATTERN}
    ))
  , ?_test(bad_expr(
      "match [([], \"hi\", 3.0)] {\n"
      "  [(a)] => a\n"
      "  [(_, _, c) | _] => c\n"
      "}",
      {"Float", "([A], String, Float)", l(2, 21, 1), ?FROM_MATCH_BODY}
    ))
  , ?_test(bad_expr(
      "(|[a | _], a| a)(['a'], 'a')",
      {?ERR_REDEF("a", l(3, 1)), l(11, 1)}
    ))
  , ?_test(bad_prg(
      "enum Foo<A> { Bar(Atom), Baz(A) }\n"
      "f(Bar(x), [Baz(y), Baz(x) | _]) = y",
      {?ERR_REDEF("x", l(1, 6, 1)), l(1, 23, 1)}
    ))
  , ?_test(bad_prg(
      "enum Foo { Bar, Baz(Int) }\n"
      "expr = match Baz(5) { Baz => 1 }",
      {?ERR_ARITY(0, 1), l(1, 22, 3)}
    ))
  , ?_test(bad_prg(
      "enum Foo { Bar, Baz(Int) }\n"
      "expr = match Baz(5) { Baz(1, 2) => 1 }",
      {?ERR_ARITY(2, 1), l(1, 22, 9)}
    ))
  , ?_test(bad_prg(
      "enum Foo { Bar, Baz(Int) }\n"
      "expr = match Bar { Bar(2) => 1 }",
      {?ERR_ARITY(1, 0), l(1, 19, 6)}
    ))
  , ?_test(bad_prg(
      "exception Baz(Int)\n"
      "expr = match Baz(5) { Baz => 1 }",
      {?ERR_ARITY(0, 1), l(1, 22, 3)}
    ))
  , ?_test(bad_prg(
      "exception Baz(Int)\n"
      "expr = match Baz(5) { Baz(1, 2) => 1 }",
      {?ERR_ARITY(2, 1), l(1, 22, 9)}
    ))
  , ?_test(bad_prg(
      "exception Bar\n"
      "expr = match Bar { Bar(2) => 1 }",
      {?ERR_ARITY(1, 0), l(1, 19, 6)}
    ))
  , ?_test(bad_prg(
      "struct Foo { a : Int }\n"
      "expr = match Foo(1) { Foo(1) => 1 }",
      {?ERR_MATCH_STRUCT, l(1, 22, 3)}
    ))


  , ?_test("[A]" = ok_expr(
      "let 3 = 3\n"
      "[]"
    ))
  , ?_test("(Int, Float)" = ok_expr(
      "let [_, (x, _, _)] = [(1, \"foo\", @foo), (2, \"bar\", @bar)]\n"
      "(x + 3 : Int, x + 3.0)"
    ))
  , ?_test("((A, B)) -> A" = ok_prg(
      "f(t) =\n"
      "  let (a, _) = t\n"
      "  a",
      "f"
    ))
  , ?_test(bad_expr(
      "let true = 3\n"
      "[]",
      {"Bool", "A ~ Num", l(4, 4), ?FROM_LET}
    ))
  , ?_test(bad_expr(
      "let [_, (x, _)] = [\"foo\", \"bar\"]\n"
      "x",
      {"[(A, B)]", "[String]", l(4, 11), ?FROM_LET}
    ))
  , ?_test(bad_expr(
      "let (a, b, a) = (3, 7, 3)\n",
      {?ERR_REDEF("a", l(5, 1)), l(11, 1)}
    ))
  , ?_test(bad_prg(
      "f(t) =\n"
      "  let (a, _) = t\n"
      "  a\n"
      "g(t) = f(t) : B",
      {
        type_system:rigid_err(
          "A",
          "B",
          ?FROM_EXPR_SIG,
          ?ERR_RIGID_BOUND("B", "A")
        ),
        l(3, 7, 8)
      }
    ))
  % regression: match expr inferred multiple times
  , ?_test(bad_expr(
      "match x { @a => true, @b => false }",
      {?ERR_NOT_DEF("x"), l(6, 1)}
    ))


  , ?_test("()" = ok_expr("if let a = 3.0 then a"))
  % to ensure env is reset appropriately
  , ?_test("Bool" = ok_expr(
      "let a = true\n"
      "if let a = 3.0 then a\n"
      "a"
    ))
  , ?_test("Bool" = ok_expr(
      "let a = true\n"
      "if let a = 3.0 then a else 5\n"
      "a"
    ))
  , ?_test("String" = ok_expr(
      "if let (2, a) = (1, \"hi\") then a else \"hey\""
    ))
  , ?_test("Float" = ok_expr(
      "if let f = |b| if b then f(!b) + 1 else 1.5\n"
      "then f(true)\n"
      "else 0"
    ))
  , ?_test(bad_expr(
      "if let a = 3.0 then a else true",
      {"Float", "Bool", l(27, 4), ?FROM_ELSE_BODY}
    ))
  , ?_test(bad_expr(
      "if let (_, a) = [\"hello\", \"hi\"] then a else \"hey\"",
      {"(A, B)", "[String]", l(7, 6), ?FROM_IF_LET_PATTERN}
    ))
  ].

exhaustive_test_() ->
  [ ?_test("Atom" = ok_expr("match 0 { a => @hi }"))
  , ?_test(bad_expr(
      "match 0 { 0 => @hi }",
      {?ERR_MISSING_CASE("_"), l(0, 20)}
    ))

  , ?_test("A ~ Num" = ok_expr("match () { () => 1 }"))
  % Can't write a program that fails to exhaustively match ().

  , ?_test("Char" = ok_expr("match true { true => 't', false => 'f' }"))
  , ?_test(bad_expr(
      "match true { true => 't' }",
      {?ERR_MISSING_CASE("false"), l(0, 26)}
    ))
  , ?_test(bad_expr(
      "match true { false => 'f' }",
      {?ERR_MISSING_CASE("true"), l(0, 27)}
    ))

  , ?_test("Bool" = ok_expr("match [] { [] => true, [h | t] => false }"))
  , ?_test(bad_expr(
      "match [] { [h | t] => false }",
      {?ERR_MISSING_CASE("[]"), l(0, 29)}
    ))
  , ?_test(bad_expr(
      "match [] { [] => true }",
      {?ERR_MISSING_CASE("[_ | _]"), l(0, 23)}
    ))

  , ?_test("Float" = ok_expr(
      "match [true] {\n"
      "  [true] => 1.2\n"
      "  [false] => 2.5\n"
      "  [true, false, true] => 0\n"
      "  [_, true | t] => 1.2\n"
      "  [true, false | t] => 2.5\n"
      "  [false, false | t] => 2.5\n"
      "  [] => 3\n"
      "}"
    ))
  , ?_test(bad_expr(
      "match [true] {\n"
      "  [true] => 1.2\n"
      "  [false] => 2.5\n"
      "  [true, false, true] => 0\n"
      "  [_, true | t] => 1.2\n"
      "  [true, false | t] => 2.5\n"
      "  [] => 3\n"
      "}",
      {?ERR_MISSING_CASE("[false, false | _]"), l(0, 0, 7, 1)}
    ))
  , ?_test(bad_expr(
      "match [true] {\n"
      "  [true] => 1.2\n"
      "  [true, false, true] => 0\n"
      "  [_, true | t] => 1.2\n"
      "  [true, false | t] => 2.5\n"
      "  [false, false | t] => 2.5\n"
      "  [] => 3\n"
      "}",
      {?ERR_MISSING_CASE("[false]"), l(0, 0, 7, 1)}
    ))
  , ?_test(bad_expr(
      "match [true] {\n"
      "  [false] => 2.5\n"
      "  [true, false, true] => 0\n"
      "  [_, true | t] => 1.2\n"
      "  [true, false | t] => 2.5\n"
      "  [false, false | t] => 2.5\n"
      "  [] => 3\n"
      "}",
      {?ERR_MISSING_CASE("[true]"), l(0, 0, 7, 1)}
    ))

  , ?_test("()" = ok_expr("match (3.5, true, \"hey\") { (a, b, c) => () }"))
  , ?_test("()" = ok_expr(
      "match (3.5, true, \"hey\") { (_, true, c) => (), (a, false, _) => () }"
    ))
  , ?_test(bad_expr(
      "match (3.5, true, \"hey\") { (_, false, x) => () }",
      {?ERR_MISSING_CASE("(_, true, _)"), l(0, 48)}
    ))
  , ?_test(bad_expr(
      "match (3.5, true, \"hey\") { (1, false, x) => (), (_, true, y) => () }",
      {?ERR_MISSING_CASE("(_, false, _)"), l(0, 68)}
    ))

  , ?_test("Int" = ok_prg(
      "enum Foo { Foo, Bar(Int, [Atom]) }\n"
      "expr = match Foo { Foo => 1, Bar(a, _) => a }",
      "expr"
    ))
  , ?_test(bad_prg(
      "enum Foo { Foo, Bar(Int, [Atom]) }\n"
      "expr = match Foo { Bar(a, _) => a }",
      {?ERR_MISSING_CASE("Foo"), l(1, 7, 28)}
    ))
  , ?_test(bad_prg(
      "enum Foo { Foo, Bar(Int, [Atom]) }\n"
      "expr = match Foo { Foo => 1, Bar(a, []) => a }",
      {?ERR_MISSING_CASE("Bar(_, [_ | _])"), l(1, 7, 39)}
    ))
  , ?_test(bad_prg(
      "enum Foo { Foo, Bar(Int, [Atom]) }\n"
      "expr = match Foo { Foo => 1, Bar(2, b) => 2 }",
      {?ERR_MISSING_CASE("Bar(_, _)"), l(1, 7, 38)}
    ))
  ].
