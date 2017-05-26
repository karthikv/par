-module(par_test).
-export([run/0]).
-include_lib("eunit/include/eunit.hrl").

run() ->
  par:reload(false),

  code:soft_purge(?MODULE),
  {ok, _} = compile:file(?MODULE),
  code:load_file(?MODULE),

  ?MODULE:test().

norm_prg(Prg, Name) ->
  {ok, Env, _} = par:infer_prg(Prg),
  #{Name := T} = Env,

  {ok, Pid} = tv_server:start_link(),
  {NormT, _} = norm(T, {#{}, Pid}),
  ok = tv_server:stop(Pid),
  NormT.

ok_prg(Prg, Name) ->
  par:pretty(norm_prg(Prg, Name)).

bad_prg(Prg, {Exp1, Exp2}) ->
  {errors, Errs} = par:infer_prg(Prg),
  [{T1, T2}] = Errs,
  check({T1, T2}, {Exp1, Exp2});

bad_prg(Prg, ExpErrs) ->
  {errors, Errs} = par:infer_prg(Prg),

  % for simplicitly, we assume errors are in the same order
  lists:foldl(fun({Err, ExpErr}, Valid) ->
    Valid and check(Err, ExpErr)
  end, true, lists:zip(Errs, ExpErrs)).

check({T1, T2}, {Exp1, Exp2}) ->
  {ok, Pid} = tv_server:start_link(),
  {NormT1, N} = norm(T1, {#{}, Pid}),
  {NormT2, _} = norm(T2, N),
  ok = tv_server:stop(Pid),

  case {par:pretty(NormT1), par:pretty(NormT2)} of
    {Exp1, Exp2} -> true;
    {Exp2, Exp1} -> true;
    _ ->
      {ok, FlipPid} = tv_server:start_link(),
      {FlipNormT2, FlipN} = norm(T2, {#{}, FlipPid}),
      {FlipNormT1, _} = norm(T1, FlipN),
      ok = tv_server:stop(FlipPid),

      case {par:pretty(FlipNormT1), par:pretty(FlipNormT2)} of
        {Exp1, Exp2} -> true;
        {Exp2, Exp1} -> true
      end
  end.

ok_expr(Expr) ->
  par:pretty(norm_prg("expr = " ++ Expr, "expr")).

bad_expr(Expr, Err) ->
  bad_prg("expr = " ++ Expr, Err).

% We don't use par:fvs() and par:subs() to implement this because it'll
% normalize variables in an arbitrary order (e.g. C -> D could become B ->
% A instead of A -> B). By doing it ourselves, we always guarantee
% a left-to-right normalization.
norm({lam, ArgT, ReturnT}, N) ->
  {NormArgT, N1} = norm(ArgT, N),
  {NormReturnT, N2} = norm(ReturnT, N1),
  {{lam, NormArgT, NormReturnT}, N2};
norm({tuple, LeftT, RightT}, N) ->
  {NormLeftT, N1} = norm(LeftT, N),
  {NormRightT, N2} = norm(RightT, N1),
  {{tuple, NormLeftT, NormRightT}, N2};
norm({tv, V, I, Cat}, {Subs, Pid}) ->
  {NewV, N1} = case maps:find(V, Subs) of
    {ok, V1} -> {V1, {Subs, Pid}};
    error ->
      V1 = tv_server:next_name(Pid),
      {V1, {Subs#{V => V1}, Pid}}
  end,

  if
    is_map(I) ->
      {{record, _, NormI}, N2} = norm({record, none, I}, N1),
      {{tv, NewV, NormI, Cat}, N2};
    true -> {{tv, NewV, I, Cat}, N1}
  end;
norm({con, Con}, N) -> {{con, Con}, N};
norm({gen, Con, ParamT}, N) ->
  {NormParamT, N1} = norm(ParamT, N),
  {{gen, Con, NormParamT}, N1};
norm({A, Options}, N) when A == either; A == ambig ->
  {NormOptions, N1} = lists:mapfoldl(fun(O, FoldN) ->
    norm(O, FoldN)
  end, N, Options),
  {{A, NormOptions}, N1};
norm({record, A, FieldMap}, N) ->
  {NewFieldMap, N1} = maps:fold(fun(Name, FieldT, {FoldMap, FoldN}) ->
    {NormT, FoldN1} = norm(FieldT, FoldN),
    {FoldMap#{Name => NormT}, FoldN1}
  end, {#{}, N}, FieldMap),
  {{record, A, NewFieldMap}, N1};
norm(none, N) -> {none, N}.

expr_test_() ->
  [ ?_test("()" = ok_expr("()"))
  , ?_test("A: Num" = ok_expr("1"))
  , ?_test("A: Num" = ok_expr("517"))
  , ?_test("Float" = ok_expr("1.0"))
  , ?_test("Float" = ok_expr("0.517"))
  , ?_test("Bool" = ok_expr("true"))
  , ?_test("Bool" = ok_expr("false"))
  , ?_test("String" = ok_expr("\"\""))
  , ?_test("String" = ok_expr("\"some string\n\""))
  , ?_test("Atom" = ok_expr("@hello"))
  , ?_test("Atom" = ok_expr("@\"hello world\""))

  , ?_test("[A]" = ok_expr("[]"))
  , ?_test("[A: Num]" = ok_expr("[3, 5, 6]"))
  , ?_test("[Float]" = ok_expr("[3, 5.0, 6]"))
  , ?_test("[Bool]" = ok_expr("[true, false, true]"))
  , ?_test(bad_expr("[3.0, true]", {"Float", "Bool"}))

  , ?_test("(Bool, Float)" = ok_expr("(true, 3.0)"))
  , ?_test("(A: Num, B: Num, [C: Num])" = ok_expr("(1, 2, [30, 40])"))
  , ?_test("((A: Num, Bool), Float)" = ok_expr("((3, false), 4.0)"))
  , ?_test("(A: Num, Bool, Float)" = ok_expr("(3, (false, 4.0))"))

  , ?_test("Map<A, B>" = ok_expr("{}"))
  , ?_test("Map<String, String>" = ok_expr("{\"key\" => \"value\"}"))
  , ?_test("Map<A: Num, Float>" = ok_expr("{1 => 2, 3 => 4.0}"))
  , ?_test(bad_expr("{\"a\" => true, \"b\" => \"c\"}", {"Bool", "String"}))

  , ?_test("Set<A>" = ok_expr("#[]"))
  , ?_test("Set<A: Num>" = ok_expr("#[1, 2]"))
  , ?_test("Set<Float>" = ok_expr("#[3, 4.0]"))
  , ?_test(bad_expr("#1", {"[A]", "B: Num"}))
  , ?_test(bad_expr("#\"some str\"", {"[A]", "String"}))
  , ?_test(bad_expr("#[\"hi\", true]", {"Bool", "String"}))

  , ?_test("Bool" = ok_expr("1 == 2"))
  , ?_test("Bool" = ok_expr("1.0 == 2.0"))
  , ?_test("Bool" = ok_expr("1.0 == 2"))
  , ?_test("Bool" = ok_expr("1 != 2"))
  , ?_test("Bool" = ok_expr("1.0 != 2.0"))
  , ?_test("Bool" = ok_expr("1 != 2.0"))
  , ?_test("Bool" = ok_expr("true == false"))
  , ?_test("Bool" = ok_expr("true != false"))
  , ?_test(bad_expr("1 == true", {"A: Num", "Bool"}))
  , ?_test(bad_expr("1 != true", {"A: Num", "Bool"}))

  , ?_test("Bool" = ok_expr("true || false"))
  , ?_test("Bool" = ok_expr("true && false"))
  , ?_test(bad_expr("true || 1", {"A: Num", "Bool"}))
  , ?_test(bad_expr("1 && false", {"A: Num", "Bool"}))

  , ?_test("Bool" = ok_expr("1 > 2"))
  , ?_test("Bool" = ok_expr("1.2 > 2.34"))
  , ?_test("Bool" = ok_expr("1.1 > 2"))

  , ?_test("Bool" = ok_expr("1 < 2"))
  , ?_test("Bool" = ok_expr("1.2 < 2.34"))
  , ?_test("Bool" = ok_expr("1 < 2.34"))

  , ?_test("Bool" = ok_expr("1 >= 2"))
  , ?_test("Bool" = ok_expr("1.2 >= 2.34"))
  , ?_test("Bool" = ok_expr("1.1 >= 2"))

  , ?_test("Bool" = ok_expr("1 <= 2"))
  , ?_test("Bool" = ok_expr("1.2 <= 2.34"))
  , ?_test("Bool" = ok_expr("1 <= 2.34"))

  , ?_test(bad_expr("true > 1", {"Bool", "A: Num"}))
  , ?_test(bad_expr("true <= 1", {"Bool", "A: Num"}))

  , ?_test("A: Num" = ok_expr("100 + 50"))
  , ?_test("Float" = ok_expr("100.1 + 50.23"))
  , ?_test("Float" = ok_expr("100 + 50.23"))
  , ?_test(bad_expr("true + 30", {"Bool", "A: Num"}))

  , ?_test("A: Num" = ok_expr("100 - 50"))
  , ?_test("Float" = ok_expr("100.1 - 50.23"))
  , ?_test("Float" = ok_expr("100.1 - 50"))
  , ?_test(bad_expr("true - 30.0", {"Bool", "A: Num"}))

  , ?_test("A: Num" = ok_expr("100 * 50"))
  , ?_test("Float" = ok_expr("100.1 * 50.23"))
  , ?_test("Float" = ok_expr("100.1 * 50"))
  , ?_test(bad_expr("30 * false", {"Bool", "A: Num"}))

  , ?_test("Float" = ok_expr("100 / 50"))
  , ?_test("Float" = ok_expr("100.1 / 50.23"))
  , ?_test("Float" = ok_expr("100.1 / 50"))
  , ?_test(bad_expr("30 / false", {"Bool", "A: Num"}))

  , ?_test("A: Num" = ok_expr("5 % 3"))
  , ?_test(bad_expr("5.3 % 3", {"Float", "Int"}))

  , ?_test("Float" = ok_expr("3 + 5 * 7 - 4 / 2 + 38 % 6 - 8"))
  , ?_test(bad_expr("7 - 12 / 5 % 6", {"Float", "Int"}))

  , ?_test("String" = ok_expr("\"hello \" ++ \"world\""))
  , ?_test("[A: Num]" = ok_expr("[1, 2] ++ [3, 4, 5, 6]"))
  , ?_test("[Bool]" = ok_expr("[] ++ [true, false]"))
  , ?_test("[A]" = ok_expr("[] ++ []"))
  , ?_test("Map<A, B>" = ok_expr("{} ++ {}"))
  , ?_test("Map<String, A: Num>" = ok_expr("{\"a\" => 3} ++ {}"))
  , ?_test("Set<A>" = ok_expr("#[] ++ #[]"))
  , ?_test("Set<Float>" = ok_expr("#[1, 2] ++ #[3.0]"))
  , ?_test(bad_expr("30.0 ++ \"str\"", {"Float", "A: Concatable"}))
  , ?_test(bad_expr("[true] ++ [1, 2]", {"Bool", "A: Num"}))

  , ?_test("Set<A>" = ok_expr("#[] -- #[]"))
  , ?_test("Set<Float>" = ok_expr("#[3.0, 5.7, 6.8] -- #[3.0]"))
  , ?_test("[A]" = ok_expr("[] -- []"))
  , ?_test("[Float]" = ok_expr("[3.0, 5.7, 6.8] -- [3.0]"))
  , ?_test(bad_expr("\"hi\" -- []", {"String", "A: Separable"}))
  , ?_test(bad_expr("[1] -- #[2, 3]", {"Set<A: Num>", "[B: Num]"}))

  , ?_test("A: Num" = ok_expr("-15"))
  , ?_test("Float" = ok_expr("-15.0"))
  , ?_test("Bool" = ok_expr("!false"))
  , ?_test("Bool" = ok_expr("!(-3 == 4)"))
  , ?_test(bad_expr("-true", {"Bool", "A: Num"}))
  , ?_test(bad_expr("!15.0", {"Float", "Bool"}))
  , ?_test(bad_expr("!3 == false", {"A: Num", "Bool"}))

  , ?_test("Bool" = ok_expr("true :: Bool"))
  , ?_test("Int" = ok_expr("3 :: Int"))
  , ?_test("A: Num" = ok_expr("3 :: A: Num"))
  , ?_test("Bool -> Bool" = ok_expr("|x| x :: Bool"))
  , ?_test("A -> A" = ok_expr("(|x| x) :: A -> A"))
  , ?_test("A: Num" = ok_expr("((|x| x) :: A -> A)(3)"))
  , ?_test("(A -> B) -> A -> B" = ok_expr("(|x| x) :: (A -> B) -> A -> B"))
  , ?_test(bad_expr("true :: A", {"Bool", "all(A)"}))
  , ?_test(bad_expr("3 :: A", {"A: Num", "all(B)"}))
  , ?_test(bad_expr("5.0 :: A: Num", {"Float", "all(A: Num)"}))
  , ?_test(bad_expr("5.0 :: Int", {"Float", "Int"}))
  , ?_test(bad_expr("|x| x :: B", {"rigid(A)", "all(B)"}))
  , ?_test(bad_expr("|x| x :: B -> B", {"rigid(A)", "all(B) -> all(B)"}))

  , ?_test("A: Num" = ok_expr("7 - (3 + -5)"))
  , ?_test("Float" = ok_expr("7 - (3.0 + -5)"))
  , ?_test("Bool" = ok_expr("7 == 5.0 || !true && -8 == 3 || false != false"))

  , ?_test("A: Num" = ok_expr("if 3 == 5 then 3 else 5"))
  , ?_test("Bool" = ok_expr("if !(true && false) then false else true"))
  , ?_test("()" = ok_expr("if true then @foo"))
  , ?_test("()" = ok_expr("if false then @io:nl() :: () else discard 3"))
  , ?_test(bad_expr("if false then @io:nl() :: () else 3", {"A: Num", "()"}))
  , ?_test(bad_expr("if true then 3.0 else true", {"Float", "Bool"}))

  , ?_test("Float" = ok_expr("let x = 3.0 in x + 5"))
  , ?_test("A: Num" = ok_expr("let inc(x) = x + 1 in inc(3)"))
  , ?_test("Bool" = ok_expr("let x = |a| a in x(3) == 3 && x(true)"))
  , ?_test("A: Num" = ok_expr("let a = b + 5, b = 10 in a"))
  , ?_test("A: Num" = ok_expr(
      "let f = |x, c| if x == 0 then c else f(x - 1, c * 2) in\n"
      "  f(5, 1)"
    ))
  , ?_test(bad_expr("let x = 3.0, y = true in x - y", {"Bool", "Float"}))
  , ?_test(bad_expr("(|x| let a = x(3) in x(true))(|y| y)", {"Bool", "A: Num"}))

  , ?_test("String" = ok_expr("{ \"hello\" }"))
  , ?_test("Bool" = ok_expr("{ @foo; true }"))
  , ?_test("Map<String, A: Num>" =
             ok_expr("let x = 5 in { @erlang:hd([1]); 3.0; {\"hi\" => x} }"))

  , ?_test("() -> A: Num" = ok_expr("|-| 3"))
  , ?_test("A -> A" = ok_expr("|x| x"))
  , ?_test("A: Num -> A: Num" = ok_expr("|x| x + 3"))
  , ?_test("Float -> Float" = ok_expr("|x| x + 3.0"))
  , ?_test("(Float -> A) -> Float -> A" = ok_expr("|f, x| f(x - 3.0)"))
  , ?_test("Bool" = ok_expr("(|x| x || true)(false)"))
  , ?_test("A: Num" = ok_expr("(|a, b| a + b)(3)(4)"))
  , ?_test("A: Num -> A: Num -> A: Num" = ok_expr("|x, y| x + y"))
  , ?_test("A: Num -> A: Num -> A: Num" = ok_expr("|x| |y| x + y"))
  , ?_test(bad_expr("|x| x + true", {"A: Num", "Bool"}))
  , ?_test(bad_expr("(|x| x)(1, 2)", {"A: Num", "B: Num -> C"}))

  , ?_test("A" = ok_expr("@lists:filter(|x| x > 3, [2, 4, 6])"))
  , ?_test("Set<A: Num>" =
             ok_expr("#[3] ++ let f = @gb_sets:add/2 in f(2)(#[1])"))
  , ?_test("A" = ok_expr("@io:printable_range()"))
  , ?_test("A" = ok_expr("@io:printable_range(())"))
  , ?_test("A" = ok_expr("@io:printable_range/0((), 1, 2)"))
  , ?_test(bad_expr("@io:printable_range/0(1, 2)", {"()", "A: Num"}))

  , ?_test("String" = ok_expr("\"hello\" |> |x| x ++ \" world\""))
  , ?_test("A: Num" =
             ok_expr("let inc(x) = x + 1 in (5 |> |x| 2 * x |> inc) * 7"))
  , ?_test("Atom -> Bool" = ok_expr("let f(x, y) = x == y in @hi |> f"))
  , ?_test(bad_expr("3 |> true", {"Bool", "A: Num -> B"}))
  , ?_test(bad_expr("\"hi\" |> |x| #x", {"String", "[A]"}))
  , ?_test(bad_expr(
      "let inc(x) = x + 1 in 5 |> |x| 2 * x |> inc * 7",
      [{"A: Num -> B", "C: Num"}, {"A: Num -> A: Num", "B: Num"}]
    ))
  , ?_test(bad_expr(
      "3 |> |x| [x] |> |x| x ++ [4] |> |x| 2 * x",
      {"[A: Num]", "B: Num"}
    ))
  ].

para_poly_test_() ->
  [ ?_test("A -> A" = ok_prg("id(a) = a", "id"))
  , ?_test("(A: Num -> B) -> B" = ok_prg("foo(f) = f(3)", "foo"))
  , ?_test("(A -> B) -> (C -> A) -> C -> B" =
             ok_prg("cmp(f, g, x) = f(g(x))", "cmp"))
  , ?_test(bad_prg(
      "add(x) = x + 3\n"
      "expr = add(true)",
      {"Bool", "A: Num"}
    ))
  , ?_test(bad_prg("omega(x) = x(x)", {"A", "A -> B"}))


  , ?_test("(Bool, Float, Bool, Float)" = ok_prg(
      "foo = bar\n"
      "bar = foo\n"
      "expr = (bar :: Bool, bar :: Float, foo :: Bool, foo :: Float)",
      "expr"
    ))
  , ?_test("Bool" = ok_prg(
      "id(a) = let foo(x) = a in let a = 4 in let bar = foo(3) in bar\n"
      "expr = id(3) == 3 && id(true)",
      "expr"
    ))
  , ?_test(bad_prg(
      "id(a) = let foo(x) = a in let a = 4 in let bar = foo(3) in bar\n"
      "expr = id(3) && id(true)",
      {"A: Num", "Bool"}
    ))
  ].

recur_test_() ->
  [ ?_test("A -> B" = ok_prg("f(x) = f(x)", "f"))
  , ?_test("A: Num -> B: Num" = ok_prg(
      "fib(n) = if n == 0 || n == 1 then 1 else fib(n - 1) + fib(n - 2)",
      "fib"
    ))
  , ?_test("Float -> A: Num" = ok_prg(
      "f(x) = g(x - 10.0)\n"
      "g(x) = if x >= 0 then 10 * f(x) else 1",
      "f"
    ))
  , ?_test("A: Num -> Bool" = ok_prg(
      "f(x) = g(x - 10) == 100\n"
      "g(x) = if x >= 0 && f(x) then 10 else 1",
      "f"
    ))
  , ?_test(bad_prg(
      "f(x) = if x == 0 then 0 else f(x - 1)\n"
      "h(x) = g(true)\n"
      "g(x) = f(x)",
      {"A: Num", "Bool"}
    ))
  , ?_test(bad_prg(
      "f(x) = f(x) == 3\n"
      "g(x) = f(x)",
      {"A: Num", "Bool"}
    ))
  , ?_test(bad_prg(
      "f(n) = if n > 0 then f(n - 1) == 1 else true",
      {"Bool", "A: Num"}
    ))
  ].

sig_test_() ->
  [ ?_test("() -> A: Num" = ok_prg(
      "foo :: () -> A: Num\n"
      "foo() = 3",
      "foo"
    ))
  , ?_test("A -> A" = ok_prg(
      "id :: A -> A\n"
      "id(x) = x\n"
      "expr = id(3)",
      "id"
    ))
  , ?_test("A: Num -> A: Num -> A: Num" = ok_prg(
      "add :: A: Num -> A: Num -> A: Num\n"
      "add(x, y) = x + y",
      "add"
    ))
  , ?_test("(A -> B) -> (C -> A) -> C -> B" = ok_prg(
      "cmp :: (B -> C) -> (A -> B) -> A -> C\n"
      "cmp(f, g, x) = f(g(x))",
      "cmp"
    ))
  , ?_test("Int -> Int" = ok_prg(
      "foo :: Int -> Int\n"
      "foo(x) = x + 3",
      "foo"
    ))
  , ?_test("Int -> Int" = ok_prg(
      "foo(x) = x :: Int + 3",
      "foo"
    ))
  , ?_test("String -> (String, Bool)" = ok_prg(
      "foo :: String -> (String, Bool)\n"
      "foo(s) = (s, true)",
      "foo"
    ))
  , ?_test("[Int] -> [Int]" = ok_prg(
      "push :: [Int] -> [Int]\n"
      "push(x) = x ++ [1]",
      "push"
    ))
  , ?_test("[A] -> [A] -> Bool" = ok_prg(
      "empty :: List<A> -> List<A> -> Bool\n"
      "empty(l1, l2) = l1 ++ l2 == []",
      "empty"
    ))
  , ?_test("Map<A, B> -> Map<A, B> -> Map<A, B>" = ok_prg(
      "pick :: Map<K, V> -> Map<K, V> -> Map<K, V>\n"
      "pick(m1, m2) = m1",
      "pick"
    ))
  , ?_test("A -> Bool" = ok_prg(
      "bar :: A -> Bool\n"
      "bar(a) = bar(a) :: Bool",
      "bar"
    ))
  , ?_test("{ bar :: String, baz :: A: Num } -> String" = ok_prg(
      "foo :: { bar :: String, baz :: A: Num } -> String\n"
      "foo(x) = x.bar",
      "foo"
    ))
  , ?_test("{ A | bar :: String, baz :: B: Num } -> String" = ok_prg(
      "foo :: { A | bar :: String, baz :: B: Num } -> String\n"
      "foo = .bar",
      "foo"
    ))
  , ?_test(bad_prg(
      "foo :: () -> String\n"
      "foo() = true",
      {"String", "Bool"}
    ))
  , ?_test(bad_prg(
      "id :: A -> B\n"
      "id(x) = x",
      {"all(A)", "all(B)"}
    ))
  , ?_test(bad_prg(
      "inc :: A: Num -> A: Num\n"
      "inc(x) = x :: B: Num + 1 :: A: Num",
      {"rigid(A)", "all(B: Num)"}
    ))
  , ?_test(bad_prg(
      "foo :: Int -> Int\n"
      "foo(x) = x + 3\n"
      "bar :: A: Num -> Int\n"
      "bar(x) = foo(x)",
      {"Int", "all(A: Num)"}
    ))
  , ?_test(bad_prg(
      "push :: [Float] -> [A: Num]\n"
      "push(x) = x ++ [1.0]",
      {"all(A: Num)", "Float"}
    ))
  , ?_test(bad_prg(
      "empty :: List<A> -> List<B> -> Bool\n"
      "empty(l1, l2) = l1 ++ l2 == []",
      {"all(A)", "all(B)"}
    ))
  , ?_test(bad_prg(
      "foo :: { bar :: String, baz :: A: Num } -> String\n"
      "foo(x) = x.bar\n"
      "main() = foo({ bar = \"hi\" })",
      {"{ bar :: String }", "{ bar :: String, baz :: A: Num }"}
    ))
  ].

global_test_() ->
  [ ?_test("A: Num" = ok_prg("foo = 3", "foo"))
  , ?_test("[Bool]" = ok_prg(
      "foo = baz && false\n"
      "bar = [foo] ++ [true]\n"
      "baz = true",
      "bar"
    ))
  , ?_test("A: Num -> Float" = ok_prg(
      "foo = |x| bar(x) / 2\n"
      "bar(x) = if x == 0 then 1 else foo(x - 1) * 10",
      "foo"
    ))


  % Although the following recursive programs will fail at runtime, they should
  % pass the type checker. It's difficult to assess whether such programs are
  % correct statically, especially when there are many of mutual dependencies.
  % It's not worth making the type checker more complex for these cases,
  % especially since they shouldn't occur often.
  , ?_test("Float" = ok_prg(
      "foo = bar(7) + 5.3\n"
      "bar(x) = 3 + x",
      "foo"
    ))
  , ?_test("Int -> Int" = ok_prg(
      "foo :: Int\n"
      "foo = bar(3)\n"
      "bar(x) = foo + x",
      "bar"
    ))
  , ?_test("A: Num" = ok_prg("foo = 3 + foo", "foo"))


  , ?_test(bad_prg(
      "foo = \"hello\"\n"
      "expr = foo ++ @world",
      {"String", "Atom"}
    ))
  , ?_test(bad_prg(
      "foo :: Set<Int>\n"
      "foo = #[1, 2, 3]\n"
      "expr = #[5.0, 6] -- foo",
      {"Float", "Int"}
    ))
  ].

enum_test_() ->
  [ ?_test("Foo" = ok_prg(
      "enum Foo { Bar }\n"
      "expr = Bar",
      "expr"
    ))
  , ?_test("Foo" = ok_prg(
      "enum Foo { Bar, Baz(Int) }\n"
      "expr = Baz(5)",
      "expr"
    ))
  , ?_test("[String] -> Foo" = ok_prg(
      "enum Foo { Bar(Bool, [String]) }\n"
      "expr = Bar(true)",
      "expr"
    ))
  , ?_test("Foo<A>" = ok_prg(
      "enum Foo<A> { Bar }\n"
      "expr = Bar",
      "expr"
    ))
  , ?_test("Foo<A: Num>" = ok_prg(
      "enum Foo<A> { Bar, Baz(A) }\n"
      "expr = Baz(3)",
      "expr"
    ))
  , ?_test("CustomList<Float>" = ok_prg(
      "enum CustomList<A> { Cons(A, CustomList<A>), End }\n"
      "expr = Cons(3, Cons(5.0, End))\n",
      "expr"
    ))
  , ?_test(bad_prg(
      "enum Foo { Bar((Float, Atom)) }\n"
      "expr = Bar(([1], @atom))",
      {"[A: Num]", "Float"}
    ))
  , ?_test(bad_prg(
      "enum Foo<A> { Bar(A, A) }\n"
      "expr = Bar(3, true)",
      {"A: Num", "Bool"}
    ))
  , ?_test(bad_prg(
      "enum CustomList<A> { Cons(A, CustomList<A>), End }\n"
      "expr = Cons(\"hi\", Cons(5.0, End))\n",
      {"String", "Float"}
    ))
  ].

record_test_() ->
  % simple create/access/update record
  [ ?_test("{ bar :: A: Num }" = ok_expr("{ bar = 3 }"))
  , ?_test("{ bar :: A: Num, baz :: Bool }" =
             ok_expr("{ bar = 3, baz = true }"))
  , ?_test("{ id :: A -> A }" = ok_expr("let id(a) = a in { id = id }"))
  , ?_test("{ A | bar :: B } -> B" = ok_expr(".bar"))
  , ?_test("Atom" = ok_expr("{ bar = @hi }.bar"))
  , ?_test("{ bar :: Float }" = ok_expr("{ { bar = 3 } | bar = 4.0 }"))
  , ?_test(bad_expr(
      "{ foo = @hi }.bar",
      {"{ foo :: Atom }", "{ A | bar :: B }"}
    ))
  , ?_test(bad_expr(
      "{ { bar = 3 } | foo = 4.0 }",
      {"{ bar :: A: Num }", "{ B | foo :: Float }"}
    ))
  , ?_test(bad_expr(
      "{ { bar = 3 } | bar = true }",
      {"A: Num", "Bool"}
    ))


  % record <=> record unification
  , ?_test("Bool" = ok_expr("{ bar = 3 } == { bar = 5 }"))
  , ?_test(bad_expr("{ bar = 3 } == { bar = \"hi\" }", {"A: Num", "String"}))
  , ?_test(bad_expr(
      "{ bar = 3 } == { foo = 4 }",
      {"{ bar :: A: Num }", "{ foo :: B: Num }"}
    ))


  % record <=> iface unification
  , ?_test("Bool" = ok_expr("let f(x) = x.bar || false in f({ bar = true })"))
  , ?_test("Atom" = ok_expr("let f(x) = x.bar in f({ bar = @hi, baz = 7 })"))
  , ?_test(bad_expr(
      "let f(x) = x.bar + x.baz in f({ bar = 3 })",
      {"{ A | bar :: B: Num, baz :: B: Num }", "{ bar :: C: Num }"}
    ))


  % iface <=> iface unification
  , ?_test("{ A | bar :: B: Num, foo :: String } -> (B: Num, String)" = ok_prg(
      "f(x) = (x.bar + 4, x.foo ++ \"hi\")",
      "f"
    ))
  , ?_test(bad_prg(
      "f(x) = (x.bar + 4, x.foo ++ \"hi\", x.foo && true)",
      {"String", "Bool"}
    ))


  % occurs checks
  , ?_test(bad_expr("let a = { bar = a } in a", {"A", "{ bar :: A }"}))
  , ?_test(bad_prg(
      "f(x) = let a = { x | bar = a } in a",
      {"A", "{ B | bar :: A }"}
    ))


  % record fvs
  , ?_test(bad_prg(
      "f(x) = let a() = x.a in (a() ++ \"hi\", true && a())",
      {"String", "Bool"}
    ))


  % named struct
  , ?_test("Foo" = ok_prg(
      "struct Foo { bar :: Int }\n"
      "expr = Foo(3)",
      "expr"
    ))
  , ?_test("Foo" = ok_prg(
      "struct Foo { bar :: Int }\n"
      "expr = Foo { bar = 3 }",
      "expr"
    ))
  , ?_test("[String] -> Foo" = ok_prg(
      "struct Foo { bar :: Int, baz :: [String] }\n"
      "expr = Foo(3)",
      "expr"
    ))
  , ?_test("Foo" = ok_prg(
      "struct Foo { bar :: Int, baz :: [Atom] }\n"
      "expr = Foo { baz = [@first, @second], bar = 15 }",
      "expr"
    ))
  , ?_test("A -> Foo<Atom, A>" = ok_prg(
      "struct Foo<X, Y> { bar :: X, baz :: Y }\n"
      "expr = Foo(@hi)",
      "expr"
    ))
  , ?_test("Foo<Atom>" = ok_prg(
      "struct Foo<X> { bar :: X }\n"
      "expr = Foo { bar = @hi }",
      "expr"
    ))
  % Won't be able to create a valid Foo, but should still type check.
  , ?_test("Bool" = ok_prg(
      "struct Foo { baz :: Foo }\n"
      "expr = true",
      "expr"
    ))
  , ?_test("Foo" = ok_prg(
      "struct Foo { bar :: Atom, baz :: [Foo] }\n"
      "expr = Foo { bar = @hi, baz = [Foo { bar = @hello, baz = [] }] }",
      "expr"
    ))
  , ?_test(bad_prg(
      "struct Foo { bar :: (Float, Atom) }\n"
      "expr = Foo(([1], @a))",
      {"[A: Num]", "Float"}
    ))
  , ?_test(bad_prg(
      "struct Foo<X> { bar :: [X], baz :: Bool }\n"
      "expr = Foo { baz = true, bar = 5 }",
      {"[A]", "B: Num"}
    ))
  , ?_test(bad_prg(
      "struct Foo<A> { bar :: A, baz :: A }\n"
      "expr = Foo(3, true)",
      {"A: Num", "Bool"}
    ))


  % generalization cases
  , ?_test("(String, Bool)" = ok_prg(
      "struct Foo<A> { bar :: A }\n"
      "expr = let id(a) = a, f = Foo { bar = id } in\n"
      "  (f.bar(\"hi\"), f.bar(true))",
      "expr"
    ))
  , ?_test("{ A | foo :: B -> C } -> { D | bar :: B } -> C" = ok_prg(
      "f(x, y) = x.foo(y.bar)",
      "f"
    ))
  , ?_test(bad_prg(
      "struct Foo<A> { bar :: A }\n"
      "expr = Foo(\"hi\").bar && true",
      {"String", "Bool"}
    ))
  , ?_test(bad_prg(
      "struct Foo<A> { bar :: A }\n"
      "f(x) = (x.bar && true, x.bar ++ \"hi\")",
      {"Bool", "A: Concatable"}
    ))
  , ?_test(bad_prg(
      "f(x) = (x.bar(\"hi\"), x.bar(true))",
      {"String", "Bool"}
    ))
  , ?_test(bad_prg(
      "struct Foo<A> { bar :: A }\n"
      "expr = let id(a) = a in\n"
      "  (|f| (f.bar(\"hi\"), f.bar(true)))(Foo { bar = id })",
      {"String", "Bool"}
    ))


  % name reconciliation
  , ?_test("{ bar :: A: Num }" = ok_prg(
      "struct Foo { bar :: Int }\n"
      "expr = { bar = 3 }",
      "expr"
    ))
  , ?_test("Foo" = ok_prg(
      "struct Foo { bar :: Int }\n"
      "expr = let x = { bar = 3 } in { x == Foo { bar = 4 }; x }",
      "expr"
    ))
  , ?_test("(String, Foo<Int>)" = ok_prg(
      "struct Foo<A> { bar :: A }\n"
      "expr :: (String, Foo<Int>)\n"
      "expr = (\"hi\", { bar = 3 })",
      "expr"
    ))
  , ?_test("Bool" = ok_prg(
      "struct Foo { bar :: Int }\n"
      "struct Baz { bar :: Int }\n"
      "expr = Foo { bar = 3 } == Baz { bar = 3 }",
      "expr"
    ))
  , ?_test("Bool" = ok_prg(
      "struct Foo<A> { bar :: A }\n"
      "struct Baz { bar :: Int }\n"
      "expr = Foo { bar = 3 } == Baz { bar = 6 }",
      "expr"
    ))
  , ?_test("Bool" = ok_prg(
      "struct Foo<A> { bar :: A, baz :: String }\n"
      "struct Baz<A> { bar :: Int, baz :: A }\n"
      "expr = Foo { bar = 3, baz = \"hi\" } == Baz { bar = 3, baz = \"hi\" }",
      "expr"
    ))
  , ?_test(bad_prg(
      "struct Foo { bar :: Int }\n"
      "expr = let x = { bar = 3, baz = \"hi\" } in x == Foo { bar = 4 }",
      {"{ bar :: A: Num, baz :: String }", "{ bar :: Int }"}
    ))
  , ?_test(bad_prg(
      "struct Foo { bar :: String }\n"
      "struct Baz { bar :: Int }\n"
      "expr = Foo { bar = \"hi\" } == Baz { bar = 3 }",
      {"String", "Int"}
    ))
  , ?_test(bad_prg(
      "struct Foo<A> { bar :: A }\n"
      "expr = { bar = true } == Foo { bar = 5 }",
      {"Bool", "A: Num"}
    ))
  , ?_test(bad_prg(
      "struct Foo<A> { bar :: A, baz :: String }\n"
      "struct Baz<A> { bar :: Int, baz :: A }\n"
      "expr = Foo { bar = 3, baz = \"hi\" } == Baz { bar = 3, baz = true }",
      {"String", "Bool"}
    ))


  % signature cases
  , ?_test("Foo -> Int" = ok_prg(
      "struct Foo { bar :: Int, baz :: [String] }\n"
      "f(x) = (x :: Foo).bar",
      "f"
    ))
  , ?_test("{ A | bar :: String } -> String" = ok_prg(
      "f(x) = x.bar :: String",
      "f"
    ))
  , ?_test("Foo -> Int" = ok_prg(
      "struct Foo { bar :: Int, baz :: [String] }\n"
      "f :: Foo -> Int\n"
      "f(x) = x.bar + 5",
      "f"
    ))
  ].

pattern_test_() ->
  [ ?_test("Bool" = ok_expr("match 3 { 3 => true, 4 => false }"))
  , ?_test("A: Num" = ok_expr("let x = 3 in match x + 5 { a => a + 10 }"))
  , ?_test("Float" =
             ok_expr("match |x| x { id => let y = id(true) in id(5.0) }"))
  , ?_test("(Int, Float, Int, Float)" = ok_expr(
      "match (3, 4) {\n"
      "  (a, b) => (a + 3 :: Int, a + 3.0, b + 4 :: Int, b + 4.0)\n"
      "}"
    ))
  , ?_test("Int" = ok_prg(
      "enum Foo { Bar, Baz(Int) }\n"
      "expr = match Baz(5) { Bar => 1, Baz(x) => x }",
      "expr"
    ))
  , ?_test("[String]" = ok_expr(
      "match [\"hi\", \"hey\"] { [] => [], [s] => [s], [_ | t] => t }"
    ))
  , ?_test("((Bool, Atom), Float)" = ok_expr(
      "match (1, true, @hi) {\n"
      "  (0, b) => (b, 10),\n"
      "  (a, true, c) => ((false, c), 3 * a),\n"
      "  (a, b) => (b, a / 2)\n"
      "}"
    ))
  , ?_test("Float" = ok_expr(
      "let m = [([], \"hi\", 3.0), ([2, 3], \"hey\", 58.0)] in"
      "  match m {\n"
      "    [([h | t], _) | _] => h,\n"
      "    [_, ([], _, c)] => c,\n"
      "    [(_, _, c), ([x, y | []], _)] => c + x - y\n"
      "  }"
    ))
  , ?_test("[A: Num]" = ok_expr(
      "let x = 3, y = [2] in match [1] { *y => y ++ [1], x => x ++ [2] }"
    ))

  , ?_test(bad_expr(
      "match \"hi\" { \"hey\" => true, \"hello\" => 1 }",
      {"Bool", "A: Num"}
    ))
  , ?_test(bad_expr(
      "match \"hi\" { @hi => [1, 2], \"hello\" => [3.0, 7, 5] }",
      {"String", "Atom"}
    ))
  , ?_test(bad_prg(
      "enum Foo { Bar, Baz(Int) }\n"
      "enum Animal { Cat, Dog }\n"
      "expr = match Baz(5) { Cat => 3, Bar => 1 }",
      {"Foo", "Animal"}
    ))
  , ?_test(bad_expr(
      "match [1, 2] { [a, b] => a + b, [_ | t] => t }",
      {"[A: Num]", "B: Num"}
    ))
  , ?_test(bad_expr(
      "match (1, true, @hi) {\n"
      "  (0, b) => (b, 10),\n"
      "  (a, b, c, d) => ((b, c), a / 2)\n"
      "}",
      {"Atom", "(A, B)"}
    ))
  , ?_test(bad_expr(
      "match [([], \"hi\", 3.0)] {\n"
      "  [(a)] => a,\n"
      "  [(_, _, c) | _] => c\n"
      "}",
      {"Float", "([A], String, Float)"}
    ))
  , ?_test(bad_expr(
      "let x = 3, y = [2] in match [1] { y => y ++ [1], *x => [x] }",
      {"[A: Num]", "B: Num"}
    ))


  , ?_test("[A]" = ok_expr("let 3 = 3 in []"))
  , ?_test("(Int, Float)" = ok_expr(
      "let [_, (x, _)] = [(1, \"foo\", @foo), (2, \"bar\", @bar)] in\n"
      "  (x + 3 :: Int, x + 3.0)"
    ))
  , ?_test("A: Num" =
             ok_expr("let (*a, b, *a) = (3, 7, 3), [_, a] = [1, 3] in b"))
  , ?_test(bad_expr("let true = 3 in []", {"Bool", "A: Num"}))
  , ?_test(bad_expr("let [x] = x in x", {"A", "[A]"}))
  , ?_test(bad_expr(
      "let [_, (x, _)] = [\"foo\", \"bar\"] in x",
      {"(A, B)", "String"}
    ))
  , ?_test(bad_expr(
      "let (*a, b) = (3, 7), [_, a] = [true, false] in b",
      {"A: Num", "Bool"}
    ))


  , ?_test("()" = ok_expr("if let a = 3.0 then a"))
  , ?_test("A: Num" = ok_expr(
      "if let abs(x) = if x < 0 then abs(-x) else x then abs(-3) else 0"
    ))
  , ?_test("String" =
             ok_expr("if let (2, a) = (1, \"hi\") then a else \"hey\""))
  , ?_test("Float" = ok_expr(
      "if let [f] = [|b| if b then f(!b) + 1 else 1.5]\n"
      "then f(true)\n"
      "else 0"
    ))
  , ?_test(bad_expr("if let a = 3.0 then a else true", {"Float", "Bool"}))
  , ?_test(bad_expr(
      "if let (_, a) = [\"hello\", \"hi\"] then a else \"hey\"",
      {"(A, B)", "[String]"}
    ))
  , ?_test( bad_expr(
      "if let tuple = (tuple, 1)\n"
      "then tuple\n"
      "else 0",
      {"A", "(A, B: Num)"}
    ))
  ].
