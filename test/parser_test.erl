-module(parser_test).
-on_load(load/0).

-include_lib("eunit/include/eunit.hrl").
-define(PREFIX, "module Mod expr = ").

load() -> 'NewParser':'_@init'(gb_sets:new()).

ok_prg(Prg) ->
  {ok, Tokens} = 'Lexer':tokenize(Prg),
  {ok, Parsed} = 'NewParser':parse(Tokens),
  Parsed.

ok_expr(Expr) ->
  {module, _, _, _, Defs} = ok_prg(?PREFIX ++ Expr),
  [{global, _, _, Parsed}] = Defs,
  Parsed.

%% parser_test_() ->
%%   [ ?_test({int, _, 1} = ok_expr("1"))
%%   , ?_test({binary_op, _, '+', {int, _, 2}, {int, _, 3}} = ok_expr("2 + 3"))
%%   , ?_test({binary_op, _, '-', {int, _, 50}, {int, _, 75}} = ok_expr("50 - 75"))
%%   , ?_test({binary_op, _, '*', {int, _, 8}, {int, _, 923}} = ok_expr("8 * 923"))
%%   , ?_test({binary_op, _, '/', {int, _, 773}, {int, _, 48}} = ok_expr("773 / 48"))
%%   ].

expr_test_() ->
  [ ?_assertEqual({none, l(0, 2)}, ok_expr("()"))
  , ?_assertEqual({int, l(0, 1), 1}, ok_expr("1"))
  , ?_assertEqual({int, l(0, 3), 517}, ok_expr("517"))
  , ?_assertEqual({float, l(0, 3), 1.0}, ok_expr("1.0"))
  , ?_assertEqual({float, l(0, 5), 0.517}, ok_expr("0.517"))
  , ?_assertEqual({bool, l(0, 4), true}, ok_expr("true"))
  , ?_assertEqual({bool, l(0, 5), false}, ok_expr("false"))
  , ?_assertEqual({char, l(0, 3), $a}, ok_expr("\'a\'"))
  , ?_assertEqual({char, l(0, 4), $\n}, ok_expr("\'\\n\'"))
  , ?_assertEqual({str, l(0, 2), <<"">>}, ok_expr("\"\""))
  , ?_assertEqual(
      {str, l(0, 15), <<"some string\n">>},
      ok_expr("\"some string\\n\"")
    )
  , ?_assertEqual({atom, l(0, 6), hello}, ok_expr("@hello"))
  , ?_assertEqual({atom, l(0, 14), 'hello world'}, ok_expr("@\"hello world\""))

  %% , ?_test("[A]" = ok_expr("[]"))
  %% , ?_test("[A: Num]" = ok_expr("[3, 5, 6]"))
  %% , ?_test("[Float]" = ok_expr("[3, 5.0, 6]"))
  %% , ?_test("[Bool]" = ok_expr("[true, false, true]"))
  %% , ?_test(bad_expr("[3.0, true]", {"Float", "Bool", 1, ?FROM_LIST_ELEM}))

  %% , ?_test("(Bool, Float)" = ok_expr("(true, 3.0)"))
  %% , ?_test("(A: Num, B: Num, [C: Num])" = ok_expr("(1, 2, [30, 40])"))
  %% , ?_test("((A: Num, Bool), Float)" = ok_expr("((3, false), 4.0)"))
  %% , ?_test("(A: Num, (Bool, Float))" = ok_expr("(3, (false, 4.0))"))

  %% , ?_test("Map<A, B>" = ok_expr("{}"))
  %% , ?_test("Map<String, String>" = ok_expr("{\"key\" => \"value\"}"))
  %% , ?_test("Map<A: Num, Float>" = ok_expr("{1 => 2, 3 => 4.0}"))
  %% , ?_test(bad_expr(
  %%     "{\"a\" => true, \"b\" => \"c\"}",
  %%     {"Bool", "String", 1, ?FROM_MAP_VALUE}
  %%   ))

  %% , ?_test("Set<A>" = ok_expr("#[]"))
  %% , ?_test("Set<A: Num>" = ok_expr("#[1, 2]"))
  %% , ?_test("Set<Float>" = ok_expr("#[3, 4.0]"))
  %% , ?_test(bad_expr("#1", {"[A]", "B: Num", 1, ?FROM_OP('#')}))
  %% , ?_test(bad_expr("#\"some str\"", {"[A]", "String", 1, ?FROM_OP('#')}))
  %% , ?_test(bad_expr("#[\"hi\", true]", {"Bool", "String", 1, ?FROM_LIST_ELEM}))

  %% , ?_test("Bool" = ok_expr("1 == 2"))
  %% , ?_test("Bool" = ok_expr("1.0 == 2.0"))
  %% , ?_test("Bool" = ok_expr("1.0 == 2"))
  %% , ?_test("Bool" = ok_expr("1 != 2"))
  %% , ?_test("Bool" = ok_expr("1.0 != 2.0"))
  %% , ?_test("Bool" = ok_expr("1 != 2.0"))
  %% , ?_test("Bool" = ok_expr("true == false"))
  %% , ?_test("Bool" = ok_expr("true != false"))
  %% , ?_test(bad_expr("1 == true", {"A: Num", "Bool", 1, ?FROM_OP('==')}))
  %% , ?_test(bad_expr("1 != true", {"A: Num", "Bool", 1, ?FROM_OP('!=')}))

  %% , ?_test("Bool" = ok_expr("true || false"))
  %% , ?_test("Bool" = ok_expr("true && false"))
  %% , ?_test(bad_expr("true || 1", {"A: Num", "Bool", 1, ?FROM_OP('||')}))
  %% , ?_test(bad_expr("1 && false", {"A: Num", "Bool", 1, ?FROM_OP('&&')}))

  %% , ?_test("Bool" = ok_expr("1 > 2"))
  %% , ?_test("Bool" = ok_expr("1.2 > 2.34"))
  %% , ?_test("Bool" = ok_expr("1.1 > 2"))

  %% , ?_test("Bool" = ok_expr("1 < 2"))
  %% , ?_test("Bool" = ok_expr("1.2 < 2.34"))
  %% , ?_test("Bool" = ok_expr("1 < 2.34"))

  %% , ?_test("Bool" = ok_expr("1 >= 2"))
  %% , ?_test("Bool" = ok_expr("1.2 >= 2.34"))
  %% , ?_test("Bool" = ok_expr("1.1 >= 2"))

  %% , ?_test("Bool" = ok_expr("1 <= 2"))
  %% , ?_test("Bool" = ok_expr("1.2 <= 2.34"))
  %% , ?_test("Bool" = ok_expr("1 <= 2.34"))

  %% , ?_test(bad_expr("true > 1", {"Bool", "A: Num", 1, ?FROM_OP('>')}))
  %% , ?_test(bad_expr("true <= 1", {"Bool", "A: Num", 1, ?FROM_OP('<=')}))

  %% , ?_test("A: Num" = ok_expr("100 + 50"))
  %% , ?_test("Float" = ok_expr("100.1 + 50.23"))
  %% , ?_test("Float" = ok_expr("100 + 50.23"))
  %% , ?_test(bad_expr("true + 30", {"Bool", "A: Num", 1, ?FROM_OP('+')}))

  %% , ?_test("A: Num" = ok_expr("100 - 50"))
  %% , ?_test("Float" = ok_expr("100.1 - 50.23"))
  %% , ?_test("Float" = ok_expr("100.1 - 50"))
  %% , ?_test(bad_expr("true - 30.0", {"Bool", "A: Num", 1, ?FROM_OP('-')}))

  %% , ?_test("A: Num" = ok_expr("100 * 50"))
  %% , ?_test("Float" = ok_expr("100.1 * 50.23"))
  %% , ?_test("Float" = ok_expr("100.1 * 50"))
  %% , ?_test(bad_expr("30 * false", {"Bool", "A: Num", 1, ?FROM_OP('*')}))

  %% , ?_test("Float" = ok_expr("100 / 50"))
  %% , ?_test("Float" = ok_expr("100.1 / 50.23"))
  %% , ?_test("Float" = ok_expr("100.1 / 50"))
  %% , ?_test(bad_expr("30 / false", {"Bool", "A: Num", 1, ?FROM_OP('/')}))

  %% , ?_test("A: Num" = ok_expr("5 % 3"))
  %% , ?_test(bad_expr("5.3 % 3", {"Float", "Int", 1, ?FROM_OP('%')}))

  %% , ?_test("Float" = ok_expr("3 + 5 * 7 - 4 / 2 + 38 % 6 - 8"))
  %% , ?_test(bad_expr("7 - 12 / 5 % 6", {"Float", "Int", 1, ?FROM_OP('%')}))

  %% , ?_test("String" = ok_expr("\"hello \" ++ \"world\""))
  %% , ?_test("[Float]" = ok_expr("[3.0 | []]"))
  %% , ?_test("[Atom]" = ok_expr("[@a | [@b, @c]]"))
  %% , ?_test("[Char]" = ok_expr("['a', 'b' | ['c']]"))
  %% , ?_test("[A: Num]" = ok_expr("[1, 2] ++ [3, 4, 5, 6]"))
  %% , ?_test("[Bool]" = ok_expr("[] ++ [true, false]"))
  %% , ?_test("[A]" = ok_expr("[] ++ []"))
  %% , ?_test("Map<A, B>" = ok_expr("{} ++ {}"))
  %% , ?_test("Map<String, A: Num>" = ok_expr("{\"a\" => 3} ++ {}"))
  %% , ?_test("Set<A>" = ok_expr("#[] ++ #[]"))
  %% , ?_test("Set<Float>" = ok_expr("#[1, 2] ++ #[3.0]"))
  %% , ?_test(bad_expr("[@a | [\"hi\"]]", {"Atom", "String", 1, ?FROM_LIST_TAIL}))
  %% , ?_test(bad_expr("[@a | @b]", {"Atom", "[Atom]", 1, ?FROM_LIST_TAIL}))
  %% , ?_test(bad_expr(
  %%     "['a', 3 | ['c']]",
  %%     {"Char", "A: Num", 1, ?FROM_LIST_ELEM}
  %%   ))
  %% , ?_test(bad_expr(
  %%     "30.0 ++ \"str\"",
  %%     {"Float", "A: Concatable", 1, ?FROM_OP('++')}
  %%   ))
  %% , ?_test(bad_expr("[true] ++ [1, 2]", {"Bool", "A: Num", 1, ?FROM_OP('++')}))

  %% , ?_test("Set<A>" = ok_expr("#[] -- #[]"))
  %% , ?_test("Set<Float>" = ok_expr("#[3.0, 5.7, 6.8] -- #[3.0]"))
  %% , ?_test("[A]" = ok_expr("[] -- []"))
  %% , ?_test("[Float]" = ok_expr("[3.0, 5.7, 6.8] -- [3.0]"))
  %% , ?_test(bad_expr(
  %%     "\"hi\" -- []",
  %%     {"String", "A: Separable", 1, ?FROM_OP('--')}
  %%   ))
  %% , ?_test(bad_expr(
  %%     "[1] -- #[2, 3]",
  %%     {"Set<A: Num>", "[B: Num]", 1, ?FROM_OP('--')}
  %%   ))

  %% , ?_test("A: Num" = ok_expr("-15"))
  %% , ?_test("Float" = ok_expr("-15.0"))
  %% , ?_test("Bool" = ok_expr("!false"))
  %% , ?_test("Bool" = ok_expr("!(-3 == 4)"))
  %% , ?_test("Int" = ok_expr("$'h'"))
  %% , ?_test(bad_expr("-true", {"Bool", "A: Num", 1, ?FROM_OP('-')}))
  %% , ?_test(bad_expr("!15.0", {"Float", "Bool", 1, ?FROM_OP('!')}))
  %% , ?_test(bad_expr("!3 == false", {"A: Num", "Bool", 1, ?FROM_OP('!')}))
  %% , ?_test(bad_expr("$false", {"Bool", "Char", 1, ?FROM_OP('$')}))

  %% , ?_test("Bool" = ok_expr("true :: Bool"))
  %% , ?_test("Int" = ok_expr("3 :: Int"))
  %% , ?_test("A: Num" = ok_expr("3 :: A: Num"))
  %% , ?_test("Bool -> Bool" = ok_expr("|x| x :: Bool"))
  %% , ?_test("A -> A" = ok_expr("(|x| x) :: A -> A"))
  %% , ?_test("A: Num" = ok_expr("((|x| x) :: A -> A)(3)"))
  %% , ?_test("(A -> B) -> A -> B" = ok_expr("(|x| x) :: (A -> B) -> A -> B"))
  %% , ?_test(bad_expr("true :: A", {"Bool", "rigid(A)", 1, ?FROM_EXPR_SIG}))
  %% , ?_test(bad_expr("3 :: A", {"A: Num", "rigid(B)", 1, ?FROM_EXPR_SIG}))
  %% , ?_test(bad_expr(
  %%     "5.0 :: A: Num",
  %%     {"Float", "rigid(A: Num)", 1, ?FROM_EXPR_SIG}
  %%   ))
  %% , ?_test(bad_expr(
  %%     "5.0 :: Int",
  %%     {"Float", "Int", 1, ?FROM_EXPR_SIG}
  %%   ))
  %% , ?_test(bad_expr("|x| x :: B", {"A", "rigid(B)", 1, ?FROM_EXPR_SIG}))
  %% , ?_test(bad_expr(
  %%     "|x| x :: B -> B",
  %%     {"A", "rigid(B) -> rigid(B)", 1, ?FROM_EXPR_SIG}
  %%   ))

  %% , ?_test("A: Num" = ok_expr("7 - (3 + -5)"))
  %% , ?_test("Float" = ok_expr("7 - (3.0 + -5)"))
  %% , ?_test("Bool" = ok_expr("7 == 5.0 || !true && -8 == 3 || false != false"))

  %% , ?_test("A: Num" = ok_expr("if 3 == 5 then 3 else 5"))
  %% , ?_test("Bool" = ok_expr("if !(true && false) then false else true"))
  %% , ?_test("()" = ok_expr("if true then @foo"))
  %% , ?_test("()" = ok_expr("if false then @io:nl() :: () else discard 3"))
  %% , ?_test(bad_expr(
  %%     "if false then @io:nl() :: () else 3",
  %%     {"A: Num", "()", 1, ?FROM_IF_BODY}
  %%   ))
  %% , ?_test(bad_expr(
  %%     "if true then 3.0 else true",
  %%     {"Float", "Bool", 1, ?FROM_IF_BODY}
  %%   ))

  %% , ?_test("Float" = ok_expr("let x = 3.0 in x + 5"))
  %% , ?_test("A: Num" = ok_expr("let inc(x) = x + 1 in inc(3)"))
  %% , ?_test("Bool" = ok_expr("let x = |a| a in x(3) == 3 && x(true)"))
  %% , ?_test("A: Num" = ok_expr("let a = 10, b = a + 5 in b"))
  %% , ?_test("A: Num" = ok_expr(
  %%     "let f = |x, c| if x == 0 then c else f(x - 1, c * 2) in\n"
  %%     "  f(5, 1)"
  %%   ))
  %% , ?_test("Bool" = ok_expr("let a = 1, a = a == 1 in a"))
  %% , ?_test(bad_expr(
  %%     "let x = 3.0, y = true in x - y",
  %%     {"Bool", "Float", 1, ?FROM_OP('-')}
  %%   ))
  %% , ?_test(bad_expr(
  %%     "(|x| let a = x(3) in x(true))(|y| y)",
  %%     {"Bool", "A: Num", 1, ?FROM_APP}
  %%   ))

  %% , ?_test("String" = ok_expr("{ \"hello\" }"))
  %% , ?_test("Bool" = ok_expr("{ @foo; true }"))
  %% , ?_test("Map<String, A: Num>" =
  %%            ok_expr("let x = 5 in { @erlang:hd([1]); 3.0; {\"hi\" => x} }"))

  %% , ?_test("() -> A: Num" = ok_expr("|-| 3"))
  %% , ?_test("A -> A" = ok_expr("|x| x"))
  %% , ?_test("A: Num -> A: Num" = ok_expr("|x| x + 3"))
  %% , ?_test("Float -> Float" = ok_expr("|x| x + 3.0"))
  %% , ?_test("(Float -> A) -> Float -> A" = ok_expr("|f, x| f(x - 3.0)"))
  %% , ?_test("Bool" = ok_expr("(|x| x || true)(false)"))
  %% , ?_test("A: Num" = ok_expr("(|a, b| a + b)(3)(4)"))
  %% , ?_test("A: Num -> A: Num -> A: Num" = ok_expr("|x, y| x + y"))
  %% , ?_test("A: Num -> A: Num -> A: Num" = ok_expr("|x| |y| x + y"))
  %% , ?_test(bad_expr("|x| x + true", {"A: Num", "Bool", 1, ?FROM_OP('+')}))
  %% , ?_test(bad_expr("(|x| x)(1, 2)", {"A: Num", "B: Num -> C", 1, ?FROM_APP}))

  %% , ?_test("A" = ok_expr("@lists:filter(|x| x > 3, [2, 4, 6])"))
  %% , ?_test("Set<A: Num>" =
  %%            ok_expr("#[3] ++ let f = @gb_sets:add/2 in f(2)(#[1])"))
  %% , ?_test("A" = ok_expr("@io:printable_range()"))
  %% , ?_test("A" = ok_expr("@io:printable_range(())"))
  %% , ?_test("A" = ok_expr("@io:printable_range/0((), 1, 2)"))
  %% , ?_test(bad_expr(
  %%     "@io:printable_range/0(1, 2)",
  %%     {"()", "A: Num", 1, ?FROM_APP}
  %%   ))

  %% , ?_test("String" = ok_expr("\"hello\" |> |x| x ++ \" world\""))
  %% , ?_test("A: Num" =
  %%            ok_expr("let inc(x) = x + 1 in (5 |> |x| 2 * x |> inc) * 7"))
  %% , ?_test("Atom -> Bool" = ok_expr("let f(x, y) = x == y in @hi |> f"))
  %% , ?_test(bad_expr("3 |> true", {"Bool", "A: Num -> B", 1, ?FROM_OP('|>')}))
  %% , ?_test(bad_expr("\"hi\" |> |x| #x", {"String", "[A]", 1, ?FROM_OP('|>')}))
  %% , ?_test(bad_expr(
  %%     "let inc(x) = x + 1 in 5 |> |x| 2 * x |> inc * 7",
  %%     [{"A: Num -> B", "C: Num", 1, ?FROM_OP('|>')},
  %%      {"A: Num -> A: Num", "B: Num", 1, ?FROM_OP('*')}]
  %%   ))
  %% , ?_test(bad_expr(
  %%     "3 |> |x| [x] |> |x| x ++ [4] |> |x| 2 * x",
  %%     {"[A: Num]", "B: Num", 1, ?FROM_OP('|>')}
  %%   ))
  ].

l(Offset, Len) ->
  Start = length(?PREFIX) + 1 + Offset,
  End = Start + Len,
  #{start_line => 1, start_col => Start, end_line => 1, end_col => End}.
