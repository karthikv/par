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

bad_prg(Prg, {EP1, EP2}) ->
  {errors, Errs} = par:infer_prg(Prg),
  [{T1, T2}] = Errs,

  {ok, Pid} = tv_server:start_link(),
  {NormT1, N} = norm(T1, {#{}, Pid}),
  {NormT2, _} = norm(T2, N),
  ok = tv_server:stop(Pid),

  case {par:pretty(NormT1), par:pretty(NormT2)} of
    {EP1, EP2} -> true;
    {EP2, EP1} -> true;
    _ ->
      {ok, FlipPid} = tv_server:start_link(),
      {FlipNormT2, FlipN} = norm(T2, {#{}, FlipPid}),
      {FlipNormT1, _} = norm(T1, FlipN),
      ok = tv_server:stop(FlipPid),

      case {par:pretty(FlipNormT1), par:pretty(FlipNormT2)} of
        {EP1, EP2} -> true;
        {EP2, EP1} -> true
      end
  end.

ok_expr(Expr) ->
  {lam, none, T} = norm_prg("main() = " ++ Expr, "main"),
  par:pretty(T).

bad_expr(Expr, Err) ->
  bad_prg("main() = " ++ Expr, Err).

% TODO: apply this to norm_sig_t?
%% norm(T, {Subs, Pid}) ->
%%   NewFVs = gb_sets:filter(fun(V) ->
%%     not maps:is_key(V, Subs)
%%   end, par:fvs(T)),
%% 
%%   % TODO: use this same logic for norm_sig_type
%%   PrefixedSubs = gb_sets:fold(fun(GV, FoldSubs) ->
%%     FoldSubs#{GV => [$* | tv_server:next_name(Pid)]}
%%   end, Subs, NewFVs),
%%   StrippedSubs = maps:fold(fun(_, PrefixedV, FoldSubs) ->
%%     FoldSubs#{PrefixedV => tl(PrefixedV)}
%%   end, #{}, PrefixedSubs),
%% 
%%   NormT = par:subs(par:subs(T, PrefixedSubs), StrippedSubs),
%%   {NormT, {PrefixedSubs, Pid}}.

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
norm({tv, V, I, GVs}, {Subs, Pid}) ->
  case maps:find(V, Subs) of
    {ok, V1} -> {{tv, V1, I, GVs}, {Subs, Pid}};
    error ->
      V1 = tv_server:next_name(Pid),
      {{tv, V1, I, GVs}, {Subs#{V => V1}, Pid}}
  end;
norm({con, Con}, N) -> {{con, Con}, N};
norm({gen, Con, ParamT}, N) ->
  {NormParamT, N1} = norm(ParamT, N),
  {{gen, Con, NormParamT}, N1};
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

  , ?_test("A: Num" = ok_expr("100 - 50"))
  , ?_test("Float" = ok_expr("100.1 - 50.23"))
  , ?_test("Float" = ok_expr("100.1 - 50"))

  , ?_test("A: Num" = ok_expr("100 * 50"))
  , ?_test("Float" = ok_expr("100.1 * 50.23"))
  , ?_test("Float" = ok_expr("100.1 * 50"))

  , ?_test("Float" = ok_expr("100 / 50"))
  , ?_test("Float" = ok_expr("100.1 / 50.23"))
  , ?_test("Float" = ok_expr("100.1 / 50"))

  , ?_test(bad_expr("true + 30", {"Bool", "A: Num"}))
  , ?_test(bad_expr("true - 30.0", {"Bool", "A: Num"}))
  , ?_test(bad_expr("30 * false", {"Bool", "A: Num"}))
  , ?_test(bad_expr("30 / false", {"Bool", "A: Num"}))

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
  , ?_test(bad_expr("[1] -- #[2, 3]", {"Set<A>", "[B]"}))

  , ?_test("A: Num" = ok_expr("-15"))
  , ?_test("Float" = ok_expr("-15.0"))
  , ?_test("Bool" = ok_expr("!false"))
  , ?_test("Bool" = ok_expr("!(-3 == 4)"))
  , ?_test(bad_expr("-true", {"Bool", "A: Num"}))
  , ?_test(bad_expr("!15.0", {"Float", "Bool"}))
  , ?_test(bad_expr("!3 == false", {"A: Num", "Bool"}))

  , ?_test("Int" = ok_expr("3 :: Int"))
  , ?_test("Float" = ok_expr("5 :: Float + 2"))
  , ?_test(bad_expr("3 :: A", {"A: Num", "B"}))
  , ?_test(bad_expr("5.0 :: A: Num", {"Float", "A: Num"}))
  , ?_test(bad_expr("5.0 :: Int", {"Float", "Int"}))

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
  , ?_test("Bool" = ok_expr("let x = |a| a in x(3) == 3 && x(true)"))
  , ?_test(bad_expr("let x = 3.0, y = true in x - y", {"Bool", "Float"}))

  , ?_test("String" = ok_expr("{ \"hello\" }"))
  , ?_test("Bool" = ok_expr("{ @foo; true }"))
  , ?_test("Map<String, A: Num>" =
             ok_expr("let x = 5 in { @erlang:hd([1]); 3.0; {\"hi\" => x} }"))

  , ?_test("() -> A: Num" = ok_expr("|-| 3"))
  , ?_test("A -> A" = ok_expr("|x| x"))
  %% , ?_test("A -> A" = ok_expr("(|x| x :: T)(3)"))
  %% , ?_test(bad_expr("|x| x :: T", {"A", "for all B, B"}))
  %% , ?_test("(A -> A) -> A -> A" = ok_expr("|x| x :: T -> T"))
  , ?_test("A -> A" = ok_expr("(|x| x) :: T -> T"))
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
  ].

para_poly_test_() ->
  [ ?_test("A -> A" = ok_prg("id(a) = a", "id"))
  , ?_test("(A: Num -> B) -> B" = ok_prg("foo(f) = f(3)", "foo"))
  , ?_test("(A -> B) -> (C -> A) -> C -> B" =
             ok_prg("cmp(f, g, x) = f(g(x))", "cmp"))
  , ?_test(bad_prg("omega(x) = x(x)", {"A", "A -> B"}))
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
      "f(x) = f(x) == 3 && f(x) == true\n"
      "g(x) = f(x)",
      {"A: Num", "Bool"}
    ))
  , ?_test(bad_prg(
      "f(n) = if n > 0 then f(n - 1) == 1 else true",
      {"Bool", "A: Num"}
    ))
  ].

iface_test_() ->
  [ ?_test(bad_prg(
      "add(x) = x + 3\n"
      "main() = add(true)",
      {"Bool", "A: Num"}
    ))
  ].

sig_test_() ->
  [ ?_test("() -> A: Num" = ok_prg(
      "main :: () -> A: Num\n"
      "main() = 3",
      "main"
    ))
  , ?_test("A -> A" = ok_prg(
      "id :: A -> A\n"
      "id(x) = x\n"
      "main() = id(3)",
      "id"
    ))
  , ?_test("A: Num -> A: Num -> A: Num" = ok_prg(
      "add :: A: Num -> A: Num -> A: Num\n"
      "add(x, y) = x + y",
      "add"
    ))
  %% , ?_test("A: Num -> A: Num -> A: Num" = ok_prg(
  %%     "add :: A: Num -> A: Num -> A: Num\n"
  %%     "add(x, y) = x :: B: Num + y :: A: Num",
  %%     "add"
  %%   ))
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
  , ?_test(bad_prg(
      "main :: () -> String\n"
      "main() = true",
      {"String", "Bool"}
    ))
  , ?_test(bad_prg(
      "id :: A -> B\n"
      "id(x) = x",
      {"A", "B"}
    ))
  , ?_test(bad_prg(
      "foo :: Int -> Int\n"
      "foo(x) = x + 3\n"
      "bar :: A: Num -> Int\n"
      "bar(x) = foo(x)",
      {"Int", "A: Num"}
    ))
  , ?_test(bad_prg(
      "push :: [A: Num] -> [A: Num]\n"
      "push(x) = x ++ [1.0]",
      {"A: Num", "Float"}
    ))
  , ?_test(bad_prg(
      "empty :: List<A> -> List<B> -> Bool\n"
      "empty(l1, l2) = l1 ++ l2 == []",
      {"A", "B"}
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
      "main() = foo ++ @world",
      {"String", "Atom"}
    ))
  , ?_test(bad_prg(
      "foo :: Set<Int>\n"
      "foo = #[1, 2, 3]\n"
      "main() = #[5.0, 6] -- foo",
      {"Float", "Int"}
    ))
  ].

%% enum_test_() ->
%%   [ ?_test("Foo" = ok_prg(
%%       "enum Foo { Bar }\n"
%%       "baz = Bar",
%%       "baz"
%%     ))
%%   , ?_test("Foo" = ok_prg(
%%       "enum Foo { Bar, Other }\n"
%%       "baz = Other",
%%       "baz"
%%     ))
%%   , ?_test("[String] -> Foo" = ok_prg(
%%       "enum Foo { Bar(Bool, [String]) }\n"
%%       "baz = Bar(true)",
%%       "baz"
%%     ))
%%   , ?_test("[String] -> Foo" = bad_prg(
%%       "enum Foo { Bar(A, A) }\n"
%%       "baz = Bar(3, true)",
%%       {"A: Num", "Bool"}
%%     ))
%%   ].
