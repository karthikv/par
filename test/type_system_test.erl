-module(type_system_test).
-export([type_check/1, type_check_many/3, bad_expr/2]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/errors.hrl").

-define(TMP_MANY_DIR, "/tmp/type-system-test-many").

type_check(Prg) ->
  FullPrg = "module Mod " ++ Prg,
  type_system:infer_prg(FullPrg).

norm_prg(Prg, Name) ->
  {ok, Env, _} = type_check(Prg),
  Key = {"Mod", Name},
  #{Key := {T, _}} = Env,

  {ok, Pid} = tv_server:start_link(),
  {NormT, _} = norm(T, {#{}, Pid}),
  ok = tv_server:stop(Pid),
  NormT.

ok_prg(Prg, Name) ->
  type_system:pretty(norm_prg(Prg, Name)).

bad_prg(Prg, {Exp1, Exp2, ExpLine, ExpFrom}) ->
  {errors, [Err], _} = type_check(Prg),
  assert_err_equal(Err, {Exp1, Exp2, "Mod", ExpLine, ExpFrom});

bad_prg(Prg, ExpErrs) when is_list(ExpErrs) ->
  {errors, Errs, _} = type_check(Prg),

  % for simplicitly, we assume errors are in the same order
  lists:foreach(fun({Err, {Exp1, Exp2, ExpLine, ExpFrom}}) ->
    assert_err_equal(Err, {Exp1, Exp2, "Mod", ExpLine, ExpFrom})
  end, lists:zip(Errs, ExpErrs)).

ctx_err_prg(Prg, {ExpMsg, ExpLine}) ->
  {errors, [{Msg, "Mod", Loc}], _} = type_check(Prg),
  ?assertEqual(ExpMsg, Msg),
  ?assertEqual(ExpLine, ?START_LINE(Loc)).

ok_expr(Expr) ->
  type_system:pretty(norm_prg("expr = " ++ Expr, "expr")).

bad_expr(Expr, Err) ->
  bad_prg("expr = " ++ Expr, Err).

type_check_many(Dir, PathPrgs, TargetPath) ->
  ok = filelib:ensure_dir(Dir),
  os:cmd(["rm -rf ",  Dir]),

  lists:foreach(fun({Path, Prg}) ->
    AbsPath = filename:join(Dir, Path ++ ".par"),
    ok = filelib:ensure_dir(AbsPath),
    ok = file:write_file(AbsPath, Prg)
  end, PathPrgs),

  AbsTargetPath = filename:join(Dir, TargetPath ++ ".par"),
  type_system:infer_file(AbsTargetPath).

ok_many(PathPrgs, TargetPath, Name) ->
  {ok, Env, Comps} = type_check_many(?TMP_MANY_DIR, PathPrgs, TargetPath),
  #comp{module=Module} = hd(Comps),
  {T, _} = maps:get({Module, Name}, Env),

  {ok, Pid} = tv_server:start_link(),
  {NormT, _} = norm(T, {#{}, Pid}),
  ok = tv_server:stop(Pid),
  type_system:pretty(NormT).

bad_many(PathPrgs, TargetPath, ExpErr) ->
  {errors, [Err], _} = type_check_many(?TMP_MANY_DIR, PathPrgs, TargetPath),
  assert_err_equal(Err, ExpErr).

ctx_err_many(PathPrgs, TargetPath, {ExpMsg, ExpModule, ExpLine}) ->
  {errors, [{Msg, Module, Loc}], _} = type_check_many(
    ?TMP_MANY_DIR,
    PathPrgs,
    TargetPath
  ),
  ?assertEqual(ExpMsg, Msg),
  ?assertEqual(ExpModule, Module),
  ?assertEqual(ExpLine, ?START_LINE(Loc)).

assert_err_equal(
  {T1, T2, Module, Loc, From},
  {Exp1, Exp2, ExpModule, ExpLine, ExpFrom}
 ) ->
  {ok, Pid} = tv_server:start_link(),
  {NormT1, N} = norm(T1, {#{}, Pid}),
  {NormT2, _} = norm(T2, N),
  ok = tv_server:stop(Pid),

  case {type_system:pretty(NormT1), type_system:pretty(NormT2)} of
    {Exp1, Exp2} -> true;
    {Exp2, Exp1} -> true;
    _ ->
      {ok, FlipPid} = tv_server:start_link(),
      {FlipNormT2, FlipN} = norm(T2, {#{}, FlipPid}),
      {FlipNormT1, _} = norm(T1, FlipN),
      ok = tv_server:stop(FlipPid),

      case {type_system:pretty(FlipNormT1), type_system:pretty(FlipNormT2)} of
        {Exp1, Exp2} -> true;
        {Exp2, Exp1} -> true
      end
  end,

  ?assertEqual(ExpModule, Module),
  ?assertEqual(ExpLine, ?START_LINE(Loc)),
  ?assertEqual(ExpFrom, From).

% We don't use type_system:fvs() and type_system:subs() to implement this
% because it'll normalize variables in an arbitrary order (e.g. C -> D could
% become B -> A instead of A -> B). By doing it ourselves, we always guarantee
% a left-to-right normalization.
norm({lam, ArgT, ReturnT}, N) ->
  {NormArgT, N1} = norm(ArgT, N),
  {NormReturnT, N2} = norm(ReturnT, N1),
  {{lam, NormArgT, NormReturnT}, N2};
norm({tuple, ElemTs}, N) ->
  {NormElemTs, N1} = lists:mapfoldl(fun(T, FoldN) ->
    norm(T, FoldN)
  end, N, ElemTs),
  {{tuple, NormElemTs}, N1};
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
norm({gen, Con, ParamTs}, N) ->
  {NormParamTs, N1} = lists:mapfoldl(fun(T, FoldN) ->
    norm(T, FoldN)
  end, N, ParamTs),
  {{gen, Con, NormParamTs}, N1};
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
norm({record_ext, A, BaseT, Ext}, N) ->
  {NormBaseT, N1} = norm(BaseT, N),
  {{record, _, NewExt}, N2} = norm({record, none, Ext}, N1),
  {{record_ext, A, NormBaseT, NewExt}, N2};
norm(none, N) -> {none, N}.

expr_test_() ->
  [ ?_test("()" = ok_expr("()"))
  , ?_test("A: Num" = ok_expr("1"))
  , ?_test("A: Num" = ok_expr("517"))
  , ?_test("Float" = ok_expr("1.0"))
  , ?_test("Float" = ok_expr("0.517"))
  , ?_test("Bool" = ok_expr("true"))
  , ?_test("Bool" = ok_expr("false"))
  , ?_test("Char" = ok_expr("\'a\'"))
  , ?_test("Char" = ok_expr("\'\\n\'"))
  , ?_test("String" = ok_expr("\"\""))
  , ?_test("String" = ok_expr("\"some string\\n\""))
  , ?_test("Atom" = ok_expr("@hello"))
  , ?_test("Atom" = ok_expr("@\"hello world\""))

  , ?_test("[A]" = ok_expr("[]"))
  , ?_test("[A: Num]" = ok_expr("[3, 5, 6]"))
  , ?_test("[Float]" = ok_expr("[3, 5.0, 6]"))
  , ?_test("[Bool]" = ok_expr("[true, false, true]"))
  , ?_test(bad_expr("[3.0, true]", {"Float", "Bool", 1, ?FROM_LIST_ELEM}))

  , ?_test("(Bool, Float)" = ok_expr("(true, 3.0)"))
  , ?_test("(A: Num, B: Num, [C: Num])" = ok_expr("(1, 2, [30, 40])"))
  , ?_test("((A: Num, Bool), Float)" = ok_expr("((3, false), 4.0)"))
  , ?_test("(A: Num, (Bool, Float))" = ok_expr("(3, (false, 4.0))"))

  , ?_test("Map<A, B>" = ok_expr("{}"))
  , ?_test("Map<String, String>" = ok_expr("{\"key\" => \"value\"}"))
  , ?_test("Map<A: Num, Float>" = ok_expr("{1 => 2, 3 => 4.0}"))
  , ?_test(bad_expr(
      "{\"a\" => true, \"b\" => \"c\"}",
      {"Bool", "String", 1, ?FROM_MAP_VALUE}
    ))

  , ?_test("Set<A>" = ok_expr("#[]"))
  , ?_test("Set<A: Num>" = ok_expr("#[1, 2]"))
  , ?_test("Set<Float>" = ok_expr("#[3, 4.0]"))
  , ?_test(bad_expr("#1", {"[A]", "B: Num", 1, ?FROM_UNARY_OP('#')}))
  , ?_test(bad_expr("#\"some str\"", {"[A]", "String", 1, ?FROM_UNARY_OP('#')}))
  , ?_test(bad_expr("#[\"hi\", true]", {"Bool", "String", 1, ?FROM_LIST_ELEM}))

  , ?_test("Bool" = ok_expr("1 == 2"))
  , ?_test("Bool" = ok_expr("1.0 == 2.0"))
  , ?_test("Bool" = ok_expr("1.0 == 2"))
  , ?_test("Bool" = ok_expr("1 != 2"))
  , ?_test("Bool" = ok_expr("1.0 != 2.0"))
  , ?_test("Bool" = ok_expr("1 != 2.0"))
  , ?_test("Bool" = ok_expr("true == false"))
  , ?_test("Bool" = ok_expr("true != false"))
  , ?_test(bad_expr("1 == true", {"A: Num", "Bool", 1, ?FROM_OP_RHS('==')}))
  , ?_test(bad_expr("1 != true", {"A: Num", "Bool", 1, ?FROM_OP_RHS('!=')}))

  , ?_test("Bool" = ok_expr("true || false"))
  , ?_test("Bool" = ok_expr("true && false"))
  , ?_test(bad_expr("true || 1", {"A: Num", "Bool", 1, ?FROM_OP_RHS('||')}))
  , ?_test(bad_expr("1 && false", {"A: Num", "Bool", 1, ?FROM_OP_LHS('&&')}))

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

  , ?_test(bad_expr("true > 1", {"Bool", "A: Num", 1, ?FROM_OP_LHS('>')}))
  , ?_test(bad_expr("true <= 1", {"Bool", "A: Num", 1, ?FROM_OP_LHS('<=')}))

  , ?_test("A: Num" = ok_expr("100 + 50"))
  , ?_test("Float" = ok_expr("100.1 + 50.23"))
  , ?_test("Float" = ok_expr("100 + 50.23"))
  , ?_test(bad_expr("true + 30", {"Bool", "A: Num", 1, ?FROM_OP_LHS('+')}))

  , ?_test("A: Num" = ok_expr("100 - 50"))
  , ?_test("Float" = ok_expr("100.1 - 50.23"))
  , ?_test("Float" = ok_expr("100.1 - 50"))
  , ?_test(bad_expr("true - 30.0", {"Bool", "Float", 1, ?FROM_OP_LHS('-')}))

  , ?_test("A: Num" = ok_expr("100 * 50"))
  , ?_test("Float" = ok_expr("100.1 * 50.23"))
  , ?_test("Float" = ok_expr("100.1 * 50"))
  , ?_test(bad_expr("30 * false", {"Bool", "A: Num", 1, ?FROM_OP_RHS('*')}))

  , ?_test("Float" = ok_expr("100 / 50"))
  , ?_test("Float" = ok_expr("100.1 / 50.23"))
  , ?_test("Float" = ok_expr("100.1 / 50"))
  , ?_test(bad_expr("30 / false", {"Bool", "A: Num", 1, ?FROM_OP_RHS('/')}))

  , ?_test("A: Num" = ok_expr("5 % 3"))
  , ?_test(bad_expr("5.3 % 3", {"Float", "Int", 1, ?FROM_OP_LHS('%')}))

  , ?_test("Float" = ok_expr("3 + 5 * 7 - 4 / 2 + 38 % 6 - 8"))
  , ?_test(bad_expr("7 - 12 / 5 % 6", {"Float", "Int", 1, ?FROM_OP_LHS('%')}))

  , ?_test("String" = ok_expr("\"hello \" ++ \"world\""))
  , ?_test("[Float]" = ok_expr("[3.0 | []]"))
  , ?_test("[Atom]" = ok_expr("[@a | [@b, @c]]"))
  , ?_test("[Char]" = ok_expr("['a', 'b' | ['c']]"))
  , ?_test("[A: Num]" = ok_expr("[1, 2] ++ [3, 4, 5, 6]"))
  , ?_test("[Bool]" = ok_expr("[] ++ [true, false]"))
  , ?_test("[A]" = ok_expr("[] ++ []"))
  , ?_test("Map<A, B>" = ok_expr("{} ++ {}"))
  , ?_test("Map<String, A: Num>" = ok_expr("{\"a\" => 3} ++ {}"))
  , ?_test("Set<A>" = ok_expr("#[] ++ #[]"))
  , ?_test("Set<Float>" = ok_expr("#[1, 2] ++ #[3.0]"))
  , ?_test(bad_expr("[@a | [\"hi\"]]", {"Atom", "String", 1, ?FROM_LIST_TAIL}))
  , ?_test(bad_expr("[@a | @b]", {"Atom", "[Atom]", 1, ?FROM_LIST_TAIL}))
  , ?_test(bad_expr(
      "['a', 3 | ['c']]",
      {"Char", "A: Num", 1, ?FROM_LIST_ELEM}
    ))
  , ?_test(bad_expr(
      "30.0 ++ \"str\"",
      {"Float", "String", 1, ?FROM_OP_LHS('++')}
    ))
  , ?_test(bad_expr(
      "[true] ++ [1, 2]",
      {"Bool", "A: Num", 1, ?FROM_OP_RHS('++')}
    ))

  , ?_test("Set<A>" = ok_expr("#[] -- #[]"))
  , ?_test("Set<Float>" = ok_expr("#[3.0, 5.7, 6.8] -- #[3.0]"))
  , ?_test("[A]" = ok_expr("[] -- []"))
  , ?_test("[Float]" = ok_expr("[3.0, 5.7, 6.8] -- [3.0]"))
  , ?_test(bad_expr(
      "\"hi\" -- []",
      {"String", "[A]", 1, ?FROM_OP_LHS('--')}
    ))
  , ?_test(bad_expr(
      "[1] -- #[2, 3]",
      {"Set<A: Num>", "[B: Num]", 1, ?FROM_OP_RHS('--')}
    ))

  , ?_test("A: Num" = ok_expr("-15"))
  , ?_test("Float" = ok_expr("-15.0"))
  , ?_test("Bool" = ok_expr("!false"))
  , ?_test("Bool" = ok_expr("!(-3 == 4)"))
  , ?_test("Int" = ok_expr("$'h'"))
  , ?_test(bad_expr("-true", {"Bool", "A: Num", 1, ?FROM_UNARY_OP('-')}))
  , ?_test(bad_expr("!15.0", {"Float", "Bool", 1, ?FROM_UNARY_OP('!')}))
  , ?_test(bad_expr("!3 == false", {"A: Num", "Bool", 1, ?FROM_UNARY_OP('!')}))
  , ?_test(bad_expr("$false", {"Bool", "Char", 1, ?FROM_UNARY_OP('$')}))

  , ?_test("Bool" = ok_expr("true :: Bool"))
  , ?_test("Int" = ok_expr("3 :: Int"))
  , ?_test("A: Num" = ok_expr("3 :: A: Num"))
  , ?_test("Bool -> Bool" = ok_expr("|x| x :: Bool"))
  , ?_test("A -> A" = ok_expr("(|x| x) :: A -> A"))
  , ?_test("A: Num" = ok_expr("((|x| x) :: A -> A)(3)"))
  , ?_test("(A -> B) -> A -> B" = ok_expr("(|x| x) :: (A -> B) -> A -> B"))
  , ?_test(bad_expr("true :: A", {"Bool", "rigid(A)", 1, ?FROM_EXPR_SIG}))
  , ?_test(bad_expr("3 :: A", {"A: Num", "rigid(B)", 1, ?FROM_EXPR_SIG}))
  , ?_test(bad_expr(
      "5.0 :: A: Num",
      {"Float", "rigid(A: Num)", 1, ?FROM_EXPR_SIG}
    ))
  , ?_test(bad_expr(
      "5.0 :: Int",
      {"Float", "Int", 1, ?FROM_EXPR_SIG}
    ))
  , ?_test(bad_expr("|x| x :: B", {"A", "rigid(B)", 1, ?FROM_EXPR_SIG}))
  , ?_test(bad_expr(
      "|x| x :: B -> B",
      {"A", "rigid(B) -> rigid(B)", 1, ?FROM_EXPR_SIG}
    ))

  , ?_test("A: Num" = ok_expr("7 - (3 + -5)"))
  , ?_test("Float" = ok_expr("7 - (3.0 + -5)"))
  , ?_test("Bool" = ok_expr("7 == 5.0 || !true && -8 == 3 || false != false"))

  , ?_test("A: Num" = ok_expr("if 3 == 5 then 3 else 5"))
  , ?_test("Bool" = ok_expr("if !(true && false) then false else true"))
  , ?_test("()" = ok_expr("if true then @foo"))
  , ?_test("()" = ok_expr("if false then @io:nl() :: () else discard 3"))
  , ?_test(bad_expr(
      "if false then @io:nl() :: () else 3",
      {"A: Num", "()", 1, ?FROM_ELSE_BODY}
    ))
  , ?_test(bad_expr(
      "if true then 3.0 else true",
      {"Float", "Bool", 1, ?FROM_ELSE_BODY}
    ))

  , ?_test("Float" = ok_expr("let x = 3.0 in x + 5"))
  , ?_test("A: Num" = ok_expr("let inc(x) = x + 1 in inc(3)"))
  , ?_test("Bool" = ok_expr("let x = |a| a in x(3) == 3 && x(true)"))
  , ?_test("A: Num" = ok_expr("let a = 10, b = a + 5 in b"))
  , ?_test("A: Num" = ok_expr(
      "let f = |x, c| if x == 0 then c else f(x - 1, c * 2) in\n"
      "  f(5, 1)"
    ))
  , ?_test("Bool" = ok_expr("let a = 1, a = a == 1 in a"))
  , ?_test(bad_expr(
      "let x = 3.0, y = true in x - y",
      {"Bool", "Float", 1, ?FROM_OP_RHS('-')}
    ))
  , ?_test(bad_expr(
      "(|x| let a = x(3) in x(true))(|y| y)",
      {"Bool", "A: Num", 1, ?FROM_APP}
    ))

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
  , ?_test(bad_expr("|x| x + true", {"Bool", "A: Num", 1, ?FROM_OP_RHS('+')}))
  , ?_test(bad_expr("(|x| x)(1, 2)", {"A: Num", "B: Num -> C", 1, ?FROM_APP}))

  , ?_test("A" = ok_expr("@lists:filter(|x| x > 3, [2, 4, 6])"))
  , ?_test("Set<A: Num>" =
             ok_expr("#[3] ++ let f = @gb_sets:add/2 in f(2)(#[1])"))
  , ?_test("A" = ok_expr("@io:printable_range()"))
  , ?_test("Atom" = ok_expr("let f() = @hi in f(())"))
  , ?_test("A" = ok_expr("@io:printable_range/0((), 1, 2)"))
  , ?_test(bad_expr(
      "@io:printable_range/0(1, 2)",
      {"()", "A: Num", 1, ?FROM_APP}
    ))

  , ?_test("String" = ok_expr("\"hello\" |> |x| x ++ \" world\""))
  , ?_test("A: Num" =
             ok_expr("let inc(x) = x + 1 in (5 |> |x| 2 * x |> inc) * 7"))
  , ?_test("Atom -> Bool" = ok_expr("let f(x, y) = x == y in @hi |> f"))
  , ?_test(bad_expr(
      "3 |> true",
      {"Bool", "A: Num -> B", 1, ?FROM_OP_RHS('|>')}
    ))
  , ?_test(bad_expr(
      "\"hi\" |> |x| #x",
      {"String", "[A]", 1, ?FROM_OP_LHS('|>')}
    ))
  , ?_test(bad_expr(
      "let inc(x) = x + 1 in 5 |> |x| 2 * x |> inc * 7",
      [{"A: Num -> B", "C: Num", 1, ?FROM_OP_RHS('|>')},
       {"A: Num -> A: Num", "B: Num", 1, ?FROM_OP_LHS('*')}]
    ))
  , ?_test(bad_expr(
      "3 |> |x| [x] |> |x| x ++ [4] |> |x| 2 * x",
      {"[A: Num]", "B: Num", 1, ?FROM_OP_LHS('|>')}
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
      {"Bool", "A: Num", 2, ?FROM_APP}
    ))
  , ?_test(bad_expr("|x| x == [x]", {"A", "[A]", 1, ?FROM_OP_RHS('==')}))
  , ?_test(bad_prg("omega(x) = x(x)", {"A", "A -> B", 1, ?FROM_APP}))


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
      {"A: Num", "Bool", 2, ?FROM_OP_LHS('&&')}
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
      {"A: Num", "Bool", 2, ?FROM_APP}
    ))
  , ?_test(bad_prg(
      "f(x) = g(x) == 3\n"
      "g(x) = f(x)",
      {"A: Num", "Bool", 1, ?FROM_OP_RESULT('==')}
    ))
  , ?_test(bad_prg(
      "f(n) = if n > 0 then f(n - 1) == 1 else 1",
      {"Bool", "A: Num", 1, ?FROM_THEN_BODY}
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
      {"String", "Bool", 1, ?FROM_GLOBAL_SIG("foo")}
    ))
  , ?_test(bad_prg(
      "id :: A -> B\n"
      "id(x) = x",
      {"rigid(A)", "rigid(B)", 1, ?FROM_GLOBAL_SIG("id")}
    ))
  , ?_test(bad_prg(
      "inc(x) = x :: B: Num + 1 :: A: Num",
      {"A: Num", "rigid(B: Num)", 1, ?FROM_EXPR_SIG}
    ))
  , ?_test(bad_prg(
      "foo :: Int -> Int\n"
      "foo(x) = x + 3\n"
      "bar :: A: Num -> Int\n"
      "bar(x) = foo(x)",
      {"Int", "rigid(A: Num)", 4, ?FROM_APP}
    ))
  , ?_test(bad_prg(
      "push :: [Float] -> [A: Num]\n"
      "push(x) = x ++ [1.0]",
      {"rigid(A: Num)", "Float", 2, ?FROM_OP_RESULT('++')}
    ))
  , ?_test(bad_prg(
      "empty :: List<A> -> List<B> -> Bool\n"
      "empty(l1, l2) = l1 ++ l2 == []",
      {"rigid(A)", "rigid(B)", 2, ?FROM_OP_RHS('++')}
    ))
  , ?_test(bad_prg(
      "foo :: { bar :: String, baz :: A: Num } -> String\n"
      "foo(x) = x.bar\n"
      "main() = foo({ bar = \"hi\" })",
      {"{ bar :: String }", "{ bar :: String, baz :: A: Num }", 3, ?FROM_APP}
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


  , ?_test(bad_prg(
      "foo = \"hello\"\n"
      "expr = foo ++ @world",
      {"String", "Atom", 2, ?FROM_OP_RHS('++')}
    ))
  , ?_test(bad_prg(
      "foo :: Set<Int>\n"
      "foo = #[1, 2, 3]\n"
      "expr = #[5.0, 6] -- foo",
      {"Float", "Int", 3, ?FROM_OP_RHS('--')}
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
      {"[A: Num]", "Float", 2, ?FROM_APP}
    ))
  , ?_test(bad_prg(
      "enum Foo<A> { Bar(A, A) }\n"
      "expr = Bar(3, true)",
      {"A: Num", "Bool", 2, ?FROM_APP}
    ))
  , ?_test(bad_prg(
      "enum CustomList<A> { Cons(A, CustomList<A>), End }\n"
      "expr = Cons(\"hi\", Cons(5.0, End))\n",
      {"String", "Float", 2, ?FROM_APP}
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
  , ?_test("{ bar :: Bool }" = ok_expr("{ { bar = 3 } | bar := true }"))
  , ?_test("{ bar :: Bool, baz :: Atom }" =
             ok_expr("{ { bar = 3, baz = @hi } | bar := true, baz = @hey }"))
  , ?_test("{ bar :: Bool, baz :: Float }" =
             ok_expr("{ { bar = 3, baz = @hi } | bar := true, baz := 3.0 }"))
  , ?_test(bad_expr(
      "{ foo = @hi }.bar",
      {"{ foo :: Atom }", "{ A | bar :: B }", 1, ?FROM_FIELD_ACCESS("bar")}
    ))
  , ?_test(bad_expr(
      "{ { bar = 3 } | bar = true }",
      {"A: Num", "Bool", 1, ?FROM_RECORD_UPDATE}
    ))
  , ?_test(bad_expr(
      "{ { bar = 3, baz = @hi } | bar := true, baz = 3.0 }",
      {"Atom", "Float", 1, ?FROM_RECORD_UPDATE}
    ))
  , ?_test(bad_expr(
      "{ { bar = 3 } | foo = 4.0 }",
      {"{ bar :: A: Num }", "{ B | foo :: Float }", 1, ?FROM_RECORD_UPDATE}
    ))
  , ?_test(bad_expr(
      "{ { bar = 3 } | foo := 4.0 }",
      % record just has to contain a field foo, not necessarily of type float
      {"{ bar :: A: Num }", "{ B | foo :: C }", 1, ?FROM_RECORD_UPDATE}
    ))


  % record <=> record unification
  , ?_test("Bool" = ok_expr("{ bar = 3 } == { bar = 5 }"))
  % to avoid infinite loops from subbing anchors
  , ?_test("(Bool, Bool)" = ok_expr(
      "let x = { bar = 3 }, y = x in (x == y, x == y)"
    ))
  , ?_test(bad_expr(
      "{ bar = 3 } == { bar = \"hi\" }",
      {"A: Num", "String", 1, ?FROM_OP_RHS('==')}
    ))
  , ?_test(bad_expr(
      "{ bar = 3 } == { foo = 4 }",
      {"{ bar :: A: Num }", "{ foo :: B: Num }", 1, ?FROM_OP_RHS('==')}
    ))


  % record <=> iface unification
  , ?_test("Bool" = ok_expr("let f(x) = x.bar || false in f({ bar = true })"))
  , ?_test("Atom" = ok_expr("let f(x) = x.bar in f({ bar = @hi, baz = 7 })"))
  , ?_test(bad_expr(
      "let f(x) = x.bar + x.baz in f({ bar = 3 })",
      {"{ A | bar :: B: Num, baz :: B: Num }", "{ bar :: C: Num }",
       1, ?FROM_APP}
    ))


  % iface <=> iface unification
  , ?_test("{ A | bar :: B: Num, foo :: String } -> (B: Num, String)" = ok_prg(
      "f(x) = (x.bar + 4, x.foo ++ \"hi\")",
      "f"
    ))
  , ?_test(bad_prg(
      "f(x) = (x.bar + 4, x.foo ++ \"hi\", x.foo && true)",
      {"String", "Bool", 1, ?FROM_OP_LHS('&&')}
    ))


  % occurs checks
  , ?_test(bad_expr(
      "|a| a == { bar = a }",
      {"A", "{ bar :: A }", 1, ?FROM_OP_RHS('==')}
    ))
  , ?_test(bad_expr(
      "|x, a| a == { x | bar = a }",
      {"A", "{ B | bar :: A }", 1, ?FROM_OP_RHS('==')}
    ))
  , ?_test(bad_expr(
      "|x, a| a == { x | bar := a }",
      {"A", "{ B | bar :: A }", 1, ?FROM_OP_RHS('==')}
    ))


  % record fvs
  , ?_test(bad_prg(
      "f(x) = let a() = x.a in (true && a(), a() ++ \"hi\")",
      {"Bool", "String", 1, ?FROM_OP_LHS('++')}
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
      {"[A: Num]", "Float", 2, ?FROM_APP}
    ))
  , ?_test(bad_prg(
      "struct Foo<X> { bar :: [X], baz :: Bool }\n"
      "expr = Foo { baz = true, bar = 5 }",
      {"[A]", "B: Num", 2, ?FROM_RECORD_CREATE("Foo")}
    ))
  , ?_test(bad_prg(
      "struct Foo<A> { bar :: A, baz :: A }\n"
      "expr = Foo(3, true)",
      {"A: Num", "Bool", 2, ?FROM_APP}
    ))


  % named struct updates
  , ?_test("Foo -> Foo" = ok_prg(
      "struct Foo { bar :: Int }\n"
      "f(x) = { x :: Foo | bar = 7 }",
      "f"
    ))
  , ?_test("{ bar :: Bool }" = ok_prg(
      "struct Foo { bar :: Int }\n"
      "foo = Foo { bar = 3 }\n"
      "baz = { foo | bar := true }",
      "baz"
    ))
  , ?_test("{ bar :: Bool, baz :: [String] }" = ok_prg(
      "struct Foo<A> { bar :: A, baz :: [String] }\n"
      "foo = Foo { bar = @a, baz = [\"hi\"] }\n"
      "baz = { foo | bar := true }",
      "baz"
    ))
  , ?_test("Foo<Bool>" = ok_prg(
      "struct Foo<A> { bar :: A, baz :: [String] }\n"
      "foo = Foo { bar = @a, baz = [\"hi\"] }\n"
      "baz = Foo { foo | bar := true }",
      "baz"
    ))
  , ?_test(bad_prg(
      "struct Foo { bar :: Int }\n"
      "foo = Foo { bar = 3 }\n"
      "baz = Foo { foo | bar := true }",
      {"Bool", "Int", 3, ?FROM_RECORD_UPDATE}
    ))
  , ?_test(bad_prg(
      "struct Foo<T> { a :: Map<T, String>, b :: [(T, Int)] }\n"
      "foo = Foo { a = { @a => \"hi\" }, b = [(@b, 3)] }\n"
      "bar = Foo { foo | a = { true => \"hi\" } }",
      {"Bool", "Atom", 3, ?FROM_RECORD_UPDATE}
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
  , ?_test("(Bool, Bool)" = ok_expr(
      "let x = { a = 3 } in (x == { a = 5.0 }, x == { a = 5 })"
    ))
  , ?_test(bad_prg(
      "struct Foo<A> { bar :: A }\n"
      "expr = Foo(\"hi\").bar && true",
      {"String", "Bool", 2, ?FROM_OP_LHS('&&')}
    ))
  , ?_test(bad_prg(
      "struct Foo<A> { bar :: A }\n"
      "f(x) = (x.bar && true, x.bar ++ \"hi\")",
      {"Bool", "String", 2, ?FROM_OP_LHS('++')}
    ))
  , ?_test(bad_prg(
      "f(x) = (x.bar(\"hi\"), x.bar(true))",
      {"String", "Bool", 1, ?FROM_APP}
    ))
  , ?_test(bad_prg(
      "struct Foo<A> { bar :: A }\n"
      "expr = let id(a) = a in\n"
      "  (|f| (f.bar(\"hi\"), f.bar(true)))(Foo { bar = id })",
      {"String", "Bool", 3, ?FROM_APP}
    ))
  % We purposely sacrifice generalization power here in favor of safety. If
  % x unifies with Foo at any point in time, we expect that x really should be
  % of type Foo everywhere. The user can choose to override us by using the :=
  % operator to change a field's type.
  , ?_test(bad_prg(
      "struct Foo { a :: Int }\n"
      "expr = let x = { a = 3 } in (x == Foo { a = 5 }, { x | a = 3.0 })",
      {"Int", "Float", 2, ?FROM_RECORD_UPDATE}
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
      {"{ bar :: A: Num, baz :: String }", "{ bar :: Int }", 2,
       ?FROM_OP_RHS('==')}
    ))
  , ?_test(bad_prg(
      "struct Foo { bar :: String }\n"
      "struct Baz { bar :: Int }\n"
      "expr = Foo { bar = \"hi\" } == Baz { bar = 3 }",
      {"String", "Int", 3, ?FROM_OP_RHS('==')}
    ))
  , ?_test(bad_prg(
      "struct Foo<A> { bar :: A }\n"
      "expr = { bar = true } == Foo { bar = 5 }",
      {"Bool", "A: Num", 2, ?FROM_OP_RHS('==')}
    ))
  , ?_test(bad_prg(
      "struct Foo<A> { bar :: A, baz :: String }\n"
      "struct Baz<A> { bar :: Int, baz :: A }\n"
      "expr = Foo { bar = 3, baz = \"hi\" } == Baz { bar = 3, baz = true }",
      {"String", "Bool", 3, ?FROM_OP_RHS('==')}
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
  , ?_test("Atom" = ok_expr("match 'x' { 'y' => @hi, 'x' => @hello }"))
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
  , ?_test("Float" = ok_expr(
      "let m = [([], \"hi\", 3.0), ([2, 3], \"hey\", 58.0)] in"
      "  match m {\n"
      "    [([h | t], _, _) | _] => h,\n"
      "    [_, ([], _, c)] => c,\n"
      "    [(_, _, c), ([x, y | []], _, _)] => c + x - y\n"
      "  }"
    ))
  , ?_test("[A: Num]" = ok_expr(
      "let x = 3, y = [2] in match [1] { *y => y ++ [1], x => x ++ [2] }"
    ))
  , ?_test("A: Num" = ok_expr(
      "match @io:printable_range() {\n"
      "  (a, _) => 1,\n"
      "  [] => 2,\n"
      "  @error => 3\n"
      "}"
    ))
  , ?_test(bad_expr(
      "match \"hi\" { \"hey\" => true, \"hello\" => 1 }",
      {"Bool", "A: Num", 1, ?FROM_MATCH_BODY}
    ))
  , ?_test(bad_expr(
      "match \"hi\" { @hi => [1, 2], \"hello\" => [3.0, 7, 5] }",
      {"String", "Atom", 1, ?FROM_MATCH_PATTERN}
    ))
  , ?_test(bad_prg(
      "enum Foo { Bar, Baz(Int) }\n"
      "enum Animal { Cat, Dog }\n"
      "expr = match Baz(5) { Cat => 3, Bar => 1 }",
      {"Foo", "Animal", 3, ?FROM_MATCH_PATTERN}
    ))
  , ?_test(bad_expr(
      "match [1, 2] { [a, b] => a + b, [_ | t] => t }",
      {"[A: Num]", "B: Num", 1, ?FROM_MATCH_BODY}
    ))
  , ?_test(bad_expr(
      "match (1, true, @hi) {\n"
      "  (0, b, c) => (b, 10),\n"
      "  (a, b, c, d) => (b, a / 2)\n"
      "}",
      {"(A: Num, Bool, Atom)", "(B, C, D, E)", 3, ?FROM_MATCH_PATTERN}
    ))
  , ?_test(bad_expr(
      "match [([], \"hi\", 3.0)] {\n"
      "  [(a)] => a,\n"
      "  [(_, _, c) | _] => c\n"
      "}",
      {"Float", "([A], String, Float)", 3, ?FROM_MATCH_BODY}
    ))
  , ?_test(bad_expr(
      "let x = 3, y = [2] in match [1] { y => y ++ [1], *x => [x] }",
      {"[A: Num]", "B: Num", 1, ?FROM_MATCH_PATTERN}
    ))


  , ?_test("[A]" = ok_expr("let 3 = 3 in []"))
  , ?_test("(Int, Float)" = ok_expr(
      "let [_, (x, _, _)] = [(1, \"foo\", @foo), (2, \"bar\", @bar)] in\n"
      "  (x + 3 :: Int, x + 3.0)"
    ))
  , ?_test("A: Num" =
             ok_expr("let [_, a] = [1, 3], (*a, b, *a) = (3, 7, 3) in b"))
  , ?_test("(A, B) -> A" = ok_prg(
      "f(t) = let (a, _) = t in a",
      "f"
    ))
  , ?_test(bad_expr("let true = 3 in []", {"Bool", "A: Num", 1, ?FROM_LET}))
  , ?_test(bad_expr(
      "let [_, (x, _)] = [\"foo\", \"bar\"] in x",
      {"(A, B)", "String", 1, ?FROM_LET}
    ))
  , ?_test(bad_expr(
      "let [_, a] = [true, false], (*a, b) = (3, 7) in b",
      {"A: Num", "Bool", 1, ?FROM_LET}
    ))
  , ?_test(bad_prg(
      "f(t) = let (a, _) = t in a\n"
      "g(t) = f(t) :: B",
      {"A", "rigid(B)", 2, ?FROM_EXPR_SIG}
    ))


  , ?_test("()" = ok_expr("if let a = 3.0 then a"))
  % to ensure env is reset appropriately
  , ?_test("Bool" = ok_expr("let a = true in { if let a = 3.0 then a; a }"))
  , ?_test("Bool" =
             ok_expr("let a = true in { if let a = 3.0 then a else 5; a }"))
  , ?_test("String" =
             ok_expr("if let (2, a) = (1, \"hi\") then a else \"hey\""))
  , ?_test("Float" = ok_expr(
      "if let f = |b| if b then f(!b) + 1 else 1.5\n"
      "then f(true)\n"
      "else 0"
    ))
  , ?_test(bad_expr(
      "if let a = 3.0 then a else true",
      {"Float", "Bool", 1, ?FROM_IF_LET_BODY}
    ))
  , ?_test(bad_expr(
      "if let (_, a) = [\"hello\", \"hi\"] then a else \"hey\"",
      {"(A, B)", "[String]", 1, ?FROM_IF_LET_PATTERN}
    ))
  ].

other_errors_test_() ->
  [ ?_test(ctx_err_prg(
      "foo = 3\n"
      "foo = 4",
      {?ERR_REDEF("foo"), 2}
    ))
  , ?_test(ctx_err_prg(
      "enum Foo { Bar(Int) }\n"
      "struct Bar { foo :: Float }",
      {?ERR_REDEF("Bar"), 2}
    ))
  , ?_test(ctx_err_prg(
      "struct Bar<A> { foo :: Float }\n"
      "enum Foo<K, V> { Bar(Int) }",
      {?ERR_REDEF("Bar"), 2}
    ))
  , ?_test(ctx_err_prg(
      "enum Int { Zero }",
      {?ERR_REDEF_BUILTIN_TYPE("Int"), 1}
    ))
  , ?_test(ctx_err_prg(
      "enum Bool<A> { Stuff(A) }",
      {?ERR_REDEF_BUILTIN_TYPE("Bool"), 1}
    ))
  , ?_test(ctx_err_prg(
      "enum Foo { Bar }\n"
      "struct Foo { baz :: String }",
      {?ERR_REDEF_TYPE("Foo"), 2}
    ))
  , ?_test(ctx_err_prg(
      "struct Foo<A, B> { baz :: String }\n"
      "enum Foo<T> { Bar }",
      {?ERR_REDEF_TYPE("Foo"), 2}
    ))
  , ?_test(ctx_err_prg(
      "enum Foo<A, A> { Baz(A) }",
      {?ERR_REDEF_TV("A"), 1}
    ))
  , ?_test(ctx_err_prg(
      "struct Foo<A, A> { baz :: A }",
      {?ERR_REDEF_TV("A"), 1}
    ))
  , ?_test(ctx_err_many([
      {"foo", "\nmodule Foo a = 1"},
      {"bar", "module Foo import \"./foo\" b = 1"}
    ], "bar", {?ERR_REDEF_MODULE("Foo"), "Foo", 2}))
  , ?_test(ctx_err_prg(
      "foo :: Int",
      {?ERR_SIG_NO_DEF("foo"), 1}
    ))
  , ?_test(ctx_err_prg(
      "foo :: Int\n"
      "bar = 3",
      {?ERR_SIG_NO_DEF("foo"), 1}
    ))
  , ?_test(ctx_err_prg(
      "foo = 4\n"
      "foo :: Int\n"
      "bar = 3",
      {?ERR_SIG_NO_DEF("foo"), 2}
    ))
  , ?_test(ctx_err_prg(
      "foo :: { a :: Int, a :: Float }\n"
      "foo = { a = 3 }",
      {?ERR_DUP_FIELD("a"), 1}
    ))
  , ?_test(ctx_err_prg(
      "\nfoo = { bar = 3, baz = 4, baz = \"hi\" }",
      {?ERR_DUP_FIELD("baz"), 2}
    ))
  , ?_test(ctx_err_prg(
      "\n\nfoo = Bar { baz = 4 }",
      {?ERR_NOT_DEF_TYPE("Bar"), 3}
    ))
  , ?_test(ctx_err_prg(
      "enum Foo {\n"
      "  Bar(\n"
      "    [\n"
      "      A\n"
      "    ]\n"
      "  )\n"
      "}",
      {?ERR_TV_SCOPE("A", "Foo"), 4}
    ))
  , ?_test(ctx_err_prg(
      "struct Foo {\n"
      "  bar ::\n"
      "    [\n"
      "      A\n"
      "    ]\n"
      "}",
      {?ERR_TV_SCOPE("A", "Foo"), 4}
    ))
  , ?_test(ctx_err_prg(
      "struct Foo<A> {\n"
      "  bar :: A: Num\n"
      "}",
      {?ERR_TV_IFACE("A", "none", "Num"), 2}
    ))
  , ?_test(ctx_err_prg(
      "foo :: A: Num -> A: Concatable\n"
      "foo(a) = @io:printable_range()",
      {?ERR_TV_IFACE("A", "Num", "Concatable"), 1}
    ))
  , ?_test(ctx_err_prg("\n\n\nfoo = a\n", {?ERR_NOT_DEF("a"), 4}))
  , ?_test(ctx_err_prg("foo = 3 + foo", {?ERR_NOT_DEF("foo"), 1}))
  , ?_test(ctx_err_many([
      {"foo", "module Foo a = 1"},
      {"bar", "module Bar\nimport \"./foo\"\ny = Foo.x"}
    ], "bar", {?ERR_NOT_DEF("x", "Foo"), "Bar", 3}))
  , ?_test(ctx_err_prg("foo = \"hi\" :: Bar", {?ERR_NOT_DEF_TYPE("Bar"), 1}))
  , ?_test(ctx_err_many([
      {"foo", "module Foo a = 1"},
      {"bar", "module Bar\nimport \"./foo\"\ny = 3 :: Foo.FooType"}
    ], "bar", {?ERR_NOT_DEF_TYPE("FooType"), "Bar", 3}))
  , ?_test(ctx_err_prg(
      "\nfoo = @erlang:asdf(true)",
      {?ERR_NOT_DEF_NATIVE(erlang, "asdf", 1), 2}
    ))
  , ?_test(ctx_err_prg(
      "bar = @io:format()",
      {?ERR_NOT_DEF_NATIVE(io, "format", 0), 1}
    ))
  , ?_test(ctx_err_prg("expr = Foo.hi", {?ERR_NOT_DEF_MODULE("Foo"), 1}))
  , ?_test(ctx_err_many([
      {"foo", "module Foo x = 3"},
      {"bar", "module Bar\nimport \"./foo\"\ny = Foo.x"}
    ], "bar", {?ERR_NOT_EXPORTED("x", "Foo"), "Bar", 3}))
  , ?_test(ctx_err_prg(
      "foo :: Map<K>\n"
      "foo = {}",
      {?ERR_TYPE_PARAMS("Map", 2, 1), 1}
    ))
  , ?_test(ctx_err_prg(
      "struct Foo<A> { bar :: A }\n"
      "foo = 'a' :: Foo",
      {?ERR_TYPE_PARAMS("Foo", 1, 0), 2}
    ))
  , ?_test(ctx_err_prg(
      "enum Foo {\n"
      "  Bar(Char),\n"
      "  Baz @Bar\n"
      "}",
      {?ERR_DUP_KEY("Bar", "Bar", #{start_line => 2}), 3}
    ))
  , ?_test(ctx_err_prg(
      "enum Foo {\n"
      "  Bar(Char) @Baz,\n"
      "  Baz\n"
      "}",
      {?ERR_DUP_KEY("Baz", "Baz", #{start_line => 3}), 2}
    ))
  , ?_test(ctx_err_prg(
      "enum Foo {\n"
      "  Bar(Char),\n"
      "  Bar\n"
      "}",
      {?ERR_REDEF("Bar"), 3}
    ))
  , ?_test("Foo" = ok_prg(
      "enum Foo {\n"
      "  Bar(Char) @baz,\n"
      "  Baz\n"
      "}\n"
      "expr = Bar('h')",
      "expr"
    ))
  % ensures sig constraints are unified first for better error messages
  , ?_test(bad_prg(
      "enum Maybe<T> { Some(T), None }\n"
      "struct Result<T> { a :: Maybe<T> }\n"
      "f :: Result<T> -> Result<[T]>\n"
      "f(r) = match r {\n"
      "  Some(x) => { r | a := Some([x]) }\n"
      "}",
      {"Result<rigid(A)>", "Maybe<B>", 5, ?FROM_MATCH_PATTERN}
    ))
  ].

import_test_() ->
  [ ?_test("A: Num" = ok_many([
      {"foo", "module Foo export x = 3"},
      {"bar", "module Bar import \"./foo\" y = Foo.x + 4"}
    ], "bar", "y"))
  , ?_test("A: Num" = ok_many([
      {"foo", "module Foo export x = 3"},
      {"bar", "module Bar import \"./foo.par\" y = Foo.x + 4"}
    ], "bar", "y"))
  , ?_test("String" = ok_many([
      {"foo", "module Foo x = 3"},
      {"bar", "module Bar import \"./foo\" x = \"hi\""}
    ], "bar", "x"))
  , ?_test("Bool" = ok_many([
      {"foo", "module Foo export x = 3.0"},
      {"a/bar", "module Bar import \"../foo\" export x = Foo.x == 3.0"},
      {"b/baz", "module Baz import \"../a/bar\" export x = Bar.x || false"}
    ], "b/baz", "x"))
  , ?_test("[Atom]" = ok_many([
      {"foo", "module Foo export x = [@a] export twice(x) = [x, x]"},
      {"a/bar",
        "module Bar\n"
        "import \"../foo\"\n"
        "import \"../b/baz\"\n"
        "y = Foo.x ++ Baz.z"},
      {"b/baz",
        "module Baz\n"
        "import \"../foo\"\n"
        "export z = Foo.twice(@b)"}
    ], "a/bar", "y"))
  , ?_test("Float -> A: Num" = ok_many([
      {"foo",
        "module Foo\n"
        "import \"./bar\"\n"
        "export f(x) = Bar.g(x - 10.0)"},
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "export g(x) = if x >= 0 then 10 * Foo.f(x) else 1"}
    ], "foo", "f"))
  , ?_test("Baz" = ok_many([
      {"foo", "module Foo enum Baz { BazInt(Int) }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "x :: Foo.Baz\n"
        "x = Foo.BazInt(3)"}
    ], "bar", "x"))
  , ?_test("Baz" = ok_many([
      {"foo", "module Foo struct Baz { a :: Int }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "x :: Foo.Baz\n"
        "x = Foo.Baz(3)"}
    ], "bar", "x"))
  , ?_test("Foo" = ok_many([
      {"foo", "module Foo enum Foo { Foo(Int) }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "x :: Foo.Foo\n"
        "x = Foo.Foo(3)"}
    ], "bar", "x"))
  , ?_test("Int" = ok_many([
      {"foo", "module Foo enum Foo { Foo(Int) }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "x = match Foo.Foo(7) { Foo.Foo(n) => n }"}
    ], "bar", "x"))
  , ?_test("Baz" = ok_many([
      {"foo", "module Foo struct Baz { a :: Int }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "enum Baz { Baz(Foo.Baz) }\n"
        "x :: Baz\n"
        "x = Baz(Foo.Baz(3))"}
    ], "bar", "x"))
  , ?_test(bad_many([
      {"foo", "module Foo export x = @hello"},
      {"bar", "module Bar import \"./foo\" y = Foo.x + 4"}
    ], "bar", {"Atom", "A: Num", "Bar", 1, ?FROM_OP_LHS('+')}))
  , ?_test(bad_many([
      {"foo", "module Foo\nimport \"./bar\"\nexport f(x) = Bar.g(x) == 3"},
      {"bar", "module Bar\nimport \"./foo\"\nexport g(x) = Foo.f(x)"}
    ], "foo", {"A: Num", "Bool", "Foo", 3, ?FROM_OP_RESULT('==')}))
  ].
