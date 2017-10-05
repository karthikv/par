-module(type_system_test).
-export([type_check/1, type_check_many/3, bad_expr/2]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/common.hrl").

-define(TMP_MANY_DIR, "/tmp/type-system-test-many").
-define(PRG_PREFIX, "module Mod\n").
-define(EXPR_PREFIX, "module Mod expr =\n").

type_check(Prg) -> type_system:infer_prg(?PRG_PREFIX ++ Prg).
type_check(Prefix, Prg) -> type_system:infer_prg(Prefix ++ Prg).

norm_prg(Prefix, Prg, Name) ->
  {ok, _, #ctx{env=Env}} = type_check(Prefix, Prg),
  Key = {"Mod", Name},
  #{Key := {T, _}} = Env,

  {ok, Pid} = tv_server:start_link(),
  {NormT, _} = norm(T, {#{}, Pid}),
  ok = tv_server:stop(Pid),
  NormT.

ok_prg(Prg, Name) ->
  utils:pretty(norm_prg(?PRG_PREFIX, Prg, Name)).

bad_prg(Prg, Err) -> bad_prg(?PRG_PREFIX, Prg, Err).

bad_prg(Prefix, Prg, {Exp1, Exp2, ExpLoc, ExpFrom}) ->
  {errors, [Err], _} = type_check(Prefix, Prg),
  assert_err_equal(Err, {Exp1, Exp2, "Mod", ExpLoc, ExpFrom});

bad_prg(Prefix, Prg, ExpErrs) when is_list(ExpErrs) ->
  {errors, Errs, _} = type_check(Prefix, Prg),

  % for simplicitly, we assume errors are in the same order
  lists:foreach(fun({Err, {Exp1, Exp2, ExpLoc, ExpFrom}}) ->
    assert_err_equal(Err, {Exp1, Exp2, "Mod", ExpLoc, ExpFrom})
  end, lists:zip(Errs, ExpErrs)).

ctx_err_prg(Prg, {ExpMsg, ExpLoc}) ->
  {errors, [{Msg, "Mod", Loc}], _} = type_check(?PRG_PREFIX, Prg),
  ?assertEqual(ExpMsg, Msg),
  ?assertEqual(ExpLoc, Loc).

ok_expr(Expr) -> utils:pretty(norm_prg(?EXPR_PREFIX, Expr, "expr")).

bad_expr(Expr, Err) -> bad_prg(?EXPR_PREFIX, Expr, Err).

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
  {ok, Comps, C} = type_check_many(?TMP_MANY_DIR, PathPrgs, TargetPath),
  #ctx{env=Env} = C,
  #comp{module=Module} = hd(Comps),
  {T, _} = maps:get({Module, Name}, Env),

  {ok, Pid} = tv_server:start_link(),
  {NormT, _} = norm(T, {#{}, Pid}),
  ok = tv_server:stop(Pid),
  utils:pretty(NormT).

bad_many(PathPrgs, TargetPath, ExpErr) ->
  {errors, [Err], _} = type_check_many(?TMP_MANY_DIR, PathPrgs, TargetPath),
  assert_err_equal(Err, ExpErr).

ctx_err_many(PathPrgs, TargetPath, {ExpMsg, ExpModule, ExpLoc}) ->
  {errors, [{Msg, Module, Loc}], _} = type_check_many(
    ?TMP_MANY_DIR,
    PathPrgs,
    TargetPath
  ),
  ?assertEqual(ExpMsg, Msg),
  ?assertEqual(ExpModule, Module),
  ?assertEqual(ExpLoc, Loc).

assert_err_equal(
  {T1, T2, Module, Loc, From},
  {Exp1, Exp2, ExpModule, ExpLoc, ExpFrom}
 ) ->
  {ok, Pid} = tv_server:start_link(),
  {NormT1, N} = norm(T1, {#{}, Pid}),
  {NormT2, _} = norm(T2, N),
  ok = tv_server:stop(Pid),

  case {utils:pretty(NormT1), utils:pretty(NormT2)} of
    {Exp1, Exp2} -> true;
    {Exp2, Exp1} -> true;
    _ ->
      {ok, FlipPid} = tv_server:start_link(),
      {FlipNormT2, FlipN} = norm(T2, {#{}, FlipPid}),
      {FlipNormT1, _} = norm(T1, FlipN),
      ok = tv_server:stop(FlipPid),

      case {utils:pretty(FlipNormT1), utils:pretty(FlipNormT2)} of
        {Exp1, Exp2} -> true;
        {Exp2, Exp1} -> true
      end
  end,

  ?assertEqual(ExpModule, Module),
  ?assertEqual(ExpLoc, Loc),
  ?assertEqual(ExpFrom, From).

% We don't use type_system:fvs() and type_system:subs() to implement this
% because it'll normalize variables in an arbitrary order (e.g. C -> D could
% become B -> A instead of A -> B). By doing it ourselves, we always guarantee
% a left-to-right normalization.
norm({lam, ArgT, ReturnT}, N) ->
  {NormArgT, N1} = norm(ArgT, N),
  {NormReturnT, N2} = norm(ReturnT, N1),
  {{lam, NormArgT, NormReturnT}, N2};
norm({lam, Env, Loc, ArgT, ReturnT}, N) ->
  {NormArgT, N1} = norm(ArgT, N),
  {NormReturnT, N2} = norm(ReturnT, N1),
  {{lam, Env, Loc, NormArgT, NormReturnT}, N2};
norm({tuple, ElemTs}, N) ->
  {NormElemTs, N1} = lists:mapfoldl(fun(T, FoldN) ->
    norm(T, FoldN)
  end, N, ElemTs),
  {{tuple, NormElemTs}, N1};
norm({tv, V, Is, Cat}, {Subs, Pid}) ->
  {NewV, N1} = case maps:find(V, Subs) of
    {ok, V1} -> {V1, {Subs, Pid}};
    error ->
      V1 = tv_server:next_name(Pid),
      {V1, {Subs#{V => V1}, Pid}}
  end,
  {{tv, NewV, Is, Cat}, N1};
norm({con, Con}, N) -> {{con, Con}, N};
norm({gen, ConT, ParamTs}, N) ->
  {NormConT, N1} = norm(ConT, N),
  {NormParamTs, N2} = lists:mapfoldl(fun(T, FoldN) ->
    norm(T, FoldN)
  end, N1, ParamTs),
  {{gen, NormConT, NormParamTs}, N2};
norm({gen, V, Is, BaseT, ParamTs}, N) ->
  % Don't need to norm V; it isn't displayed.
  {NormBaseT, N1} = norm(BaseT, N),
  {{gen, _, NormParamTs}, N2} = norm({gen, {con, ""}, ParamTs}, N1),
  {{gen, V, Is, NormBaseT, NormParamTs}, N2};
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
norm(unit, N) -> {unit, N}.

l(Offset, Len) -> l(0, Offset, Len).
l(Line, Offset, Len) -> l(Line, Offset, Line, Offset + Len).
l(StartLine, StartOffset, EndLine, EndOffset) ->
  #{
    % lines are 1-indexed, and the first line is the prefix
    start_line => 2 + StartLine,
    % columns are 1-indexed
    start_col => 1 + StartOffset,
    end_line => 2 + EndLine,
    end_col => 1 + EndOffset
  }.

expr_test_() ->
  [ ?_test("()" = ok_expr("()"))
  , ?_test("A ~ Num" = ok_expr("1"))
  , ?_test("A ~ Num" = ok_expr("517"))
  , ?_test("Float" = ok_expr("1.0"))
  , ?_test("Float" = ok_expr("0.517"))
  , ?_test("Bool" = ok_expr("true"))
  , ?_test("Bool" = ok_expr("false"))
  , ?_test("Char" = ok_expr("\'a\'"))
  , ?_test("Char" = ok_expr("\'\\n\'"))
  , ?_test("String" = ok_expr("\"\""))
  , ?_test("String" = ok_expr("\"some string\\n\""))
  , ?_test("String" = ok_expr("\"some\\\nstring\""))
  , ?_test("Atom" = ok_expr("@hello"))
  , ?_test("Atom" = ok_expr("@\"hello world\""))
  , ?_test("Atom" = ok_expr("@\"\""))

  , ?_test("[A]" = ok_expr("[]"))
  , ?_test("[A ~ Num]" = ok_expr("[3, 5, 6]"))
  , ?_test("[Float]" = ok_expr("[3, 5.0, 6]"))
  , ?_test("[Bool]" = ok_expr("[true, false, true]"))
  , ?_test(bad_expr(
      "[3.0, true]",
      {"Float", "Bool", l(6, 4), ?FROM_LIST_ELEM}
    ))

  , ?_test("(Bool, Float)" = ok_expr("(true, 3.0)"))
  , ?_test("(A ~ Num, B ~ Num, [C ~ Num])" = ok_expr("(1, 2, [30, 40])"))
  , ?_test("((A ~ Num, Bool), Float)" = ok_expr("((3, false), 4.0)"))
  , ?_test("(A ~ Num, (Bool, Float))" = ok_expr("(3, (false, 4.0))"))

  , ?_test("Map<A, B>" = ok_expr("{}"))
  , ?_test("Map<String, String>" = ok_expr("{\"key\" => \"value\"}"))
  , ?_test("Map<A ~ Num, Float>" = ok_expr("{1 => 2, 3 => 4.0}"))
  , ?_test(bad_expr(
      "{\"a\" => true, \"b\" => \"c\"}",
      {"Bool", "String", l(21, 3), ?FROM_MAP_VALUE}
    ))

  , ?_test("Set<A>" = ok_expr("#[]"))
  , ?_test("Set<A ~ Num>" = ok_expr("#[1, 2]"))
  , ?_test("Set<Float>" = ok_expr("#[3, 4.0]"))
  , ?_test(bad_expr("#1", {"[A]", "B ~ Num", l(1, 1), ?FROM_UNARY_OP('#')}))
  , ?_test(bad_expr(
      "#\"some str\"",
      {"[A]", "String", l(1, 10), ?FROM_UNARY_OP('#')}
    ))
  , ?_test(bad_expr(
      "#[\"hi\", true]",
      {"Bool", "String", l(8, 4), ?FROM_LIST_ELEM}
    ))

  , ?_test("Bool" = ok_expr("1 == 2"))
  , ?_test("Bool" = ok_expr("1.0 == 2.0"))
  , ?_test("Bool" = ok_expr("1.0 == 2"))
  , ?_test("Bool" = ok_expr("1 != 2"))
  , ?_test("Bool" = ok_expr("1.0 != 2.0"))
  , ?_test("Bool" = ok_expr("1 != 2.0"))
  , ?_test("Bool" = ok_expr("true == false"))
  , ?_test("Bool" = ok_expr("true != false"))
  , ?_test(bad_expr(
      "1 == true",
      {"A ~ Num", "Bool", l(5, 4), ?FROM_OP_RHS('==')}
    ))
  , ?_test(bad_expr(
      "1 != true",
      {"A ~ Num", "Bool", l(5, 4), ?FROM_OP_RHS('!=')}
    ))

  , ?_test("Bool" = ok_expr("true || false"))
  , ?_test("Bool" = ok_expr("true && false"))
  , ?_test(bad_expr(
      "true || 1",
      {"A ~ Num", "Bool", l(8, 1), ?FROM_OP_RHS('||')}
    ))
  , ?_test(bad_expr(
      "1 && false",
      {"A ~ Num", "Bool", l(0, 1), ?FROM_OP_LHS('&&')}
    ))

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

  , ?_test("Bool" = ok_expr("\"hi\" < \"hello\""))
  , ?_test("Bool" = ok_expr("'n' > 'm'"))
  , ?_test("Bool" = ok_expr("\"some\" >= \"some\""))

  , ?_test(bad_expr(
      "@hey > @hello",
      [{"Atom", "A ~ Ord", l(7, 6), ?FROM_OP_RHS('>')},
       {"Atom", "A ~ Ord", l(0, 4), ?FROM_OP_LHS('>')}]
    ))
  , ?_test(bad_expr(
      "true > 1",
      {"Bool", "A ~ Num", l(0, 4), ?FROM_OP_LHS('>')}
    ))
  , ?_test(bad_expr(
      "\"hi\" <= 'c'",
      {"String", "Char", l(8, 3), ?FROM_OP_RHS('<=')}
    ))

  , ?_test("A ~ Num" = ok_expr("100 + 50"))
  , ?_test("Float" = ok_expr("100.1 + 50.23"))
  , ?_test("Float" = ok_expr("100 + 50.23"))
  , ?_test(bad_expr(
      "true + 30",
      {"Bool", "A ~ Num", l(0, 4), ?FROM_OP_LHS('+')}
    ))

  , ?_test("A ~ Num" = ok_expr("100 - 50"))
  , ?_test("Float" = ok_expr("100.1 - 50.23"))
  , ?_test("Float" = ok_expr("100.1 - 50"))
  , ?_test(bad_expr(
      "true - 30.0",
      {"Bool", "Float", l(0, 4), ?FROM_OP_LHS('-')}
    ))

  , ?_test("A ~ Num" = ok_expr("100 * 50"))
  , ?_test("Float" = ok_expr("100.1 * 50.23"))
  , ?_test("Float" = ok_expr("100.1 * 50"))
  , ?_test(bad_expr(
      "30 * false",
      {"Bool", "A ~ Num", l(5, 5), ?FROM_OP_RHS('*')}
    ))

  , ?_test("Float" = ok_expr("100 / 50"))
  , ?_test("Float" = ok_expr("100.1 / 50.23"))
  , ?_test("Float" = ok_expr("100.1 / 50"))
  , ?_test(bad_expr(
      "30 / false",
      {"Bool", "A ~ Num", l(5, 5), ?FROM_OP_RHS('/')}
    ))

  , ?_test("A ~ Num" = ok_expr("5 % 3"))
  , ?_test(bad_expr(
      "5.3 % 3",
      {"Float", "Int", l(0, 3), ?FROM_OP_LHS('%')}
    ))

  , ?_test("Float" = ok_expr("3 + 5 * 7 - 4 / 2 + 38 % 6 - 8"))
  , ?_test(bad_expr(
      "7 - 12 / 5 % 6",
      {"Float", "Int", l(4, 6), ?FROM_OP_LHS('%')}
    ))

  , ?_test("String" = ok_expr("\"hello \" ++ \"world\""))
  , ?_test("[Float]" = ok_expr("[3.0 | []]"))
  , ?_test("[Atom]" = ok_expr("[@a | [@b, @c]]"))
  , ?_test("[Char]" = ok_expr("['a', 'b' | ['c']]"))
  , ?_test("[A ~ Num]" = ok_expr("[1, 2] ++ [3, 4, 5, 6]"))
  , ?_test("[Bool]" = ok_expr("[] ++ [true, false]"))
  , ?_test("[A]" = ok_expr("[] ++ []"))
  , ?_test("Map<A, B>" = ok_expr("{} ++ {}"))
  , ?_test("Map<String, A ~ Num>" = ok_expr("{\"a\" => 3} ++ {}"))
  , ?_test("Set<A>" = ok_expr("#[] ++ #[]"))
  , ?_test("Set<Float>" = ok_expr("#[1, 2] ++ #[3.0]"))
  , ?_test(bad_expr(
      "[@a | [\"hi\"]]",
      {"[Atom]", "[String]", l(6, 6), ?FROM_LIST_TAIL}
    ))
  , ?_test(bad_expr("[@a | @b]", {"Atom", "[Atom]", l(6, 2), ?FROM_LIST_TAIL}))
  , ?_test(bad_expr(
      "['a', 3 | ['c']]",
      {"Char", "A ~ Num", l(6, 1), ?FROM_LIST_ELEM}
    ))
  , ?_test(bad_expr(
      "30.0 ++ \"str\"",
      {"Float", "String", l(0, 4), ?FROM_OP_LHS('++')}
    ))
  , ?_test(bad_expr(
      "[true] ++ [1, 2]",
      {"[Bool]", "[A ~ Num]", l(10, 6), ?FROM_OP_RHS('++')}
    ))

  , ?_test("Set<A>" = ok_expr("#[] -- #[]"))
  , ?_test("Set<Float>" = ok_expr("#[3.0, 5.7, 6.8] -- #[3.0]"))
  , ?_test("[A]" = ok_expr("[] -- []"))
  , ?_test("[Float]" = ok_expr("[3.0, 5.7, 6.8] -- [3.0]"))
  , ?_test(bad_expr(
      "\"hi\" -- []",
      {"String", "[A]", l(0, 4), ?FROM_OP_LHS('--')}
    ))
  , ?_test(bad_expr(
      "[1] -- #[2, 3]",
      {"Set<A ~ Num>", "[B ~ Num]", l(7, 7), ?FROM_OP_RHS('--')}
    ))

  , ?_test("A ~ Num" = ok_expr("-15"))
  , ?_test("Float" = ok_expr("-15.0"))
  , ?_test("Bool" = ok_expr("!false"))
  , ?_test("Bool" = ok_expr("!(-3 == 4)"))
  , ?_test("Int" = ok_expr("$'h'"))
  , ?_test(bad_expr("-true", {"Bool", "A ~ Num", l(1, 4), ?FROM_UNARY_OP('-')}))
  , ?_test(bad_expr("!15.0", {"Float", "Bool", l(1, 4), ?FROM_UNARY_OP('!')}))
  , ?_test(bad_expr(
      "!3 == false",
      {"A ~ Num", "Bool", l(1, 1), ?FROM_UNARY_OP('!')}
    ))
  , ?_test(bad_expr("$false", {"Bool", "Char", l(1, 5), ?FROM_UNARY_OP('$')}))

  , ?_test("Bool" = ok_expr("true : Bool"))
  , ?_test("Int" = ok_expr("3 : Int"))
  , ?_test("A ~ Num" = ok_expr("3 : A ~ Num"))
  , ?_test("Bool -> Bool" = ok_expr("|x| x : Bool"))
  , ?_test("A -> A" = ok_expr("(|x| x) : A -> A"))
  , ?_test("A ~ Num" = ok_expr("((|x| x) : A -> A)(3)"))
  , ?_test("(A -> B) -> A -> B" = ok_expr("(|x| x) : (A -> B) -> A -> B"))
  , ?_test(bad_expr(
      "true : A",
      {"Bool", "rigid(A)", l(0, 8), ?FROM_EXPR_SIG}
    ))
  , ?_test(bad_expr("3 : A", {"A ~ Num", "rigid(B)", l(0, 5), ?FROM_EXPR_SIG}))
  , ?_test(bad_expr(
      "5.0 : A ~ Num",
      {"Float", "rigid(A ~ Num)", l(0, 13), ?FROM_EXPR_SIG}
    ))
  , ?_test(bad_expr(
      "5.0 : Int",
      {"Float", "Int", l(0, 9), ?FROM_EXPR_SIG}
    ))
  , ?_test(bad_expr("|x| x : B", {"A", "rigid(B)", l(4, 5), ?FROM_EXPR_SIG}))
  , ?_test(bad_expr(
      "|x| x : B -> B",
      {"A", "rigid(B) -> rigid(B)", l(4, 10), ?FROM_EXPR_SIG}
    ))

  , ?_test("A ~ Num" = ok_expr("7 - (3 + -5)"))
  , ?_test("Float" = ok_expr("7 - (3.0 + -5)"))
  , ?_test("Bool" = ok_expr("7 == 5.0 || !true && -8 == 3 || false != false"))

  , ?_test("A ~ Num" = ok_expr("if 3 == 5 then 3 else 5"))
  , ?_test("Bool" = ok_expr("if !(true && false) then false else true"))
  , ?_test("()" = ok_expr("if true then @foo"))
  , ?_test("()" = ok_expr("if false then @io:nl() : () else discard 3"))
  , ?_test(bad_expr(
      "if false then @io:nl() : () else 3",
      {"A ~ Num", "()", l(33, 1), ?FROM_ELSE_BODY}
    ))
  , ?_test(bad_expr(
      "if true then 3.0 else true",
      {"Float", "Bool", l(22, 4), ?FROM_ELSE_BODY}
    ))

  , ?_test("Float" = ok_expr(
      "let x = 3.0\n"
      "x + 5"
    ))
  , ?_test("A ~ Num" = ok_expr(
      "let inc(x) = x + 1\n"
      "inc(3)"
    ))
  , ?_test("Bool" = ok_expr(
      "let x = |a| a\n"
      "x(3) == 3 && x(true)"
    ))
  , ?_test("A ~ Num" = ok_expr(
      "let a = 10\n"
      "let b = a + 5\n"
      "b"
    ))
  , ?_test("A ~ Num" = ok_expr(
      "let f = |x, c| if x == 0 then c else f(x - 1, c * 2)\n"
      "f(5, 1)"
    ))
  , ?_test("Bool" = ok_expr(
      "let a = 1\n"
      "let a = a == 1\n"
      "a"
    ))
  , ?_test(bad_expr(
      "let x = 3.0\n"
      "let y = true\n"
      "x - y",
      {"Bool", "Float", l(2, 4, 1), ?FROM_OP_RHS('-')}
    ))
  , ?_test(bad_expr(
      "(|x|\n"
      "  let a = x(3)\n"
      "  x(true)\n"
      ")(|y| y)",
      {"Bool", "A ~ Num", l(2, 4, 4), ?FROM_APP}
    ))

  , ?_test("Bool" = ok_expr("@foo\ntrue"))
  , ?_test("Map<String, A ~ Num>" = ok_expr(
      "let x = 5\n"
      "@erlang:hd([1])\n"
      "3.0\n"
      "{ \"hi\" => x }"
    ))

  , ?_test("() -> A ~ Num" = ok_expr("|-| 3"))
  , ?_test("A -> A" = ok_expr("|x| x"))
  , ?_test("A ~ Num -> A ~ Num" = ok_expr("|x| x + 3"))
  , ?_test("Float -> Float" = ok_expr("|x| x + 3.0"))
  , ?_test("(Float -> A) -> Float -> A" = ok_expr("|f, x| f(x - 3.0)"))
  , ?_test("Bool" = ok_expr("(|x| x || true)(false)"))
  , ?_test("A ~ Num" = ok_expr("(|a, b| a + b)(3)(4)"))
  , ?_test("A ~ Num -> A ~ Num -> A ~ Num" = ok_expr("|x, y| x + y"))
  , ?_test("A ~ Num -> A ~ Num -> A ~ Num" = ok_expr("|x| |y| x + y"))
  , ?_test(bad_expr(
      "|x| x + true",
      {"Bool", "A ~ Num", l(8, 4), ?FROM_OP_RHS('+')}
    ))
  , ?_test(bad_expr(
      "(|x| x)(1, 2)",
      {"A ~ Num -> B ~ Num -> C", "A ~ Num -> A ~ Num", l(0, 13), ?FROM_APP}
    ))

  , ?_test("A" = ok_expr("@lists:filter(|x| x > 3, [2, 4, 6])"))
  , ?_test("Set<A ~ Num>" = ok_expr(
      "let f = @gb_sets:add/2\n"
      "#[3] ++ f(2)(#[1])"
    ))
  , ?_test("A" = ok_expr("@io:printable_range()"))
  , ?_test("Atom" = ok_expr(
      "let f() = @hi\n"
      "f(())"
    ))
  , ?_test("A" = ok_expr("@io:printable_range/0((), 1, 2)"))
  , ?_test(bad_expr(
      "@io:printable_range/0(1, 2)",
      {"()", "A ~ Num", l(22, 1), ?FROM_APP}
    ))

  , ?_test("String" = ok_expr("\"hello\" |> |x| x ++ \" world\""))
  , ?_test("A ~ Num" = ok_expr(
      "let inc(x) = x + 1\n"
      "(5 |> |x| 2 * x |> inc) * 7"
    ))
  , ?_test("Atom -> Bool" = ok_expr(
      "let f(x, y) = x == y\n"
      "@hi |> f"
    ))
  , ?_test(bad_expr(
      "3 |> true",
      {"Bool", "A ~ Num -> B", l(5, 4), ?FROM_OP_RHS('|>')}
    ))
  , ?_test(bad_expr(
      "\"hi\" |> |x| #x",
      {"String", "[A]", l(0, 4), ?FROM_OP_LHS('|>')}
    ))
  , ?_test(bad_expr(
      "let inc(x) = x + 1\n"
      "5 |> |x| 2 * x |> inc * 7",
      [{"A ~ Num -> B", "C ~ Num", l(1, 18, 7), ?FROM_OP_RHS('|>')},
       {"A ~ Num -> A ~ Num", "B ~ Num", l(1, 18, 3), ?FROM_OP_LHS('*')}]
    ))
  , ?_test(bad_expr(
      "3 |> |x| [x] |> |x| x ++ [4] |> |x| 2 * x",
      {"[A ~ Num]", "B ~ Num", l(20, 8), ?FROM_OP_LHS('|>')}
    ))
  ].

para_poly_test_() ->
  [ ?_test("A -> A" = ok_prg("id(a) = a", "id"))
  , ?_test("(A ~ Num -> B) -> B" = ok_prg("foo(f) = f(3)", "foo"))
  , ?_test("(A -> B) -> (C -> A) -> C -> B" =
             ok_prg("cmp(f, g, x) = f(g(x))", "cmp"))
  , ?_test(bad_prg(
      "add(x) = x + 3\n"
      "expr = add(true)",
      {"Bool", "A ~ Num", l(1, 11, 4), ?FROM_APP}
    ))
  , ?_test(bad_expr("|x| x == [x]", {"A", "[A]", l(9, 3), ?FROM_OP_RHS('==')}))
  , ?_test(bad_prg("omega(x) = x(x)", {"A", "A -> B", l(11, 4), ?FROM_APP}))


  , ?_test("(Bool, Float, Bool, Float)" = ok_prg(
      "foo = bar\n"
      "bar = foo\n"
      "expr = (bar : Bool, bar : Float, foo : Bool, foo : Float)",
      "expr"
    ))
  , ?_test("Bool" = ok_prg(
      "id(a) =\n"
      "  let foo(x) = a\n"
      "  let a = 4\n"
      "  let bar = foo(3)\n"
      "  bar\n"
      "expr = id(3) == 3 && id(true)",
      "expr"
    ))
  , ?_test(bad_prg(
      "id(a) =\n"
      "  let foo(x) = a\n"
      "  let a = 4\n"
      "  let bar = foo(3)\n"
      "  bar\n"
      "expr = id(3) && id(true)",
      {"A ~ Num", "Bool", l(5, 7, 5), ?FROM_OP_LHS('&&')}
    ))
  ].

recur_test_() ->
  [ ?_test("A -> B" = ok_prg("f(x) = f(x)", "f"))
  , ?_test("A ~ Num -> B ~ Num" = ok_prg(
      "fib(n) = if n == 0 || n == 1 then 1 else fib(n - 1) + fib(n - 2)",
      "fib"
    ))
  , ?_test("Float -> A ~ Num" = ok_prg(
      "f(x) = g(x - 10.0)\n"
      "g(x) = if x >= 0 then 10 * f(x) else 1",
      "f"
    ))
  , ?_test("A ~ Num -> Bool" = ok_prg(
      "f(x) = g(x - 10) == 100\n"
      "g(x) = if x >= 0 && f(x) then 10 else 1",
      "f"
    ))
  , ?_test("A ~ ToInt -> Int" = ok_prg(
      "interface ToInt { to_int : T -> Int }\n"
      "impl ToInt for Float { to_int(f) = @erlang:round(f) }\n"
      "f : A ~ ToInt -> Int\n"
      "f(a) = if to_int(a) < 10 then to_int(a) else f(1.0)",
      "f"
    ))
  , ?_test(bad_prg(
      "f(x) = if x == 0 then 0 else f(x - 1)\n"
      "h(x) = g(true)\n"
      "g(x) = f(x)",
      {"A ~ Num", "Bool", l(1, 9, 4), ?FROM_APP}
    ))
  , ?_test(bad_prg(
      "f(x) = g(x) == 3\n"
      "g(x) = f(x)",
      {"A ~ Num", "Bool", l(7, 9), ?FROM_OP_RESULT('==')}
    ))
  , ?_test(bad_prg(
      "f(n) = if n > 0 then f(n - 1) == 1 else 1",
      {"Bool", "A ~ Num", l(21, 13), ?FROM_THEN_BODY}
    ))
  ].

sig_test_() ->
  [ ?_test("() -> A ~ Num" = ok_prg(
      "foo : () -> A ~ Num\n"
      "foo() = 3",
      "foo"
    ))
  , ?_test("A -> A" = ok_prg(
      "id : A -> A\n"
      "id(x) = x\n"
      "expr = id(3)",
      "id"
    ))
  , ?_test("A ~ Num -> A ~ Num -> A ~ Num" = ok_prg(
      "add : A ~ Num -> A ~ Num -> A ~ Num\n"
      "add(x, y) = x + y",
      "add"
    ))
  , ?_test("(A -> B) -> (C -> A) -> C -> B" = ok_prg(
      "cmp : (B -> C) -> (A -> B) -> A -> C\n"
      "cmp(f, g, x) = f(g(x))",
      "cmp"
    ))
  , ?_test("Int -> Int" = ok_prg(
      "foo : Int -> Int\n"
      "foo(x) = x + 3",
      "foo"
    ))
  , ?_test("Int -> Int" = ok_prg(
      "foo(x) = x : Int + 3",
      "foo"
    ))
  , ?_test("String -> (String, Bool)" = ok_prg(
      "foo : String -> (String, Bool)\n"
      "foo(s) = (s, true)",
      "foo"
    ))
  , ?_test("[Int] -> [Int]" = ok_prg(
      "push : [Int] -> [Int]\n"
      "push(x) = x ++ [1]",
      "push"
    ))
  , ?_test("[A] -> [A] -> Bool" = ok_prg(
      "empty : List<A> -> List<A> -> Bool\n"
      "empty(l1, l2) = l1 ++ l2 == []",
      "empty"
    ))
  , ?_test("Map<A, B> -> Map<A, B> -> Map<A, B>" = ok_prg(
      "pick : Map<K, V> -> Map<K, V> -> Map<K, V>\n"
      "pick(m1, m2) = m1",
      "pick"
    ))
  , ?_test("A -> Bool" = ok_prg(
      "bar : A -> Bool\n"
      "bar(a) = bar(a) : Bool",
      "bar"
    ))
  , ?_test("{ bar : String, baz : A ~ Num } -> String" = ok_prg(
      "foo : { bar : String, baz : A ~ Num } -> String\n"
      "foo(x) = x.bar",
      "foo"
    ))
  , ?_test("{ A | bar : String, baz : B ~ Num } -> String" = ok_prg(
      "foo : { A | bar : String, baz : B ~ Num } -> String\n"
      "foo = .bar",
      "foo"
    ))
  , ?_test("A ~ Num" = ok_prg(
      "foo : A ~ Num\n"
      "foo = 1 : B ~ Num",
      "foo"
    ))
  , ?_test(bad_prg(
      "foo : () -> String\n"
      "foo() = true",
      {"() -> String", "() -> Bool", l(0, 18), ?FROM_GLOBAL_SIG("foo")}
    ))
  , ?_test(bad_prg(
      "id : A -> B\n"
      "id(x) = x",
      {"rigid(A) -> rigid(B)", "rigid(A) -> rigid(A)", l(0, 11),
       ?FROM_GLOBAL_SIG("id")}
    ))
  , ?_test(bad_prg(
      "inc(x) = x : B ~ Num + 1 : A ~ Num",
      {"A ~ Num", "rigid(B ~ Num)", l(9, 11), ?FROM_EXPR_SIG}
    ))
  , ?_test(bad_prg(
      "foo : Int -> Int\n"
      "foo(x) = x + 3\n"
      "bar : A ~ Num -> Int\n"
      "bar(x) = foo(x)",
      {"Int", "rigid(A ~ Num)", l(3, 13, 1), ?FROM_APP}
    ))
  , ?_test(bad_prg(
      "push : [Float] -> [A ~ Num]\n"
      "push(x) = x ++ [1.0]",
      {"[rigid(A ~ Num)]", "[Float]", l(1, 10, 10), ?FROM_OP_RESULT('++')}
    ))
  , ?_test(bad_prg(
      "empty : List<A> -> List<B> -> Bool\n"
      "empty(l1, l2) = l1 ++ l2 == []",
      {"[rigid(A)]", "[rigid(B)]", l(1, 22, 2), ?FROM_OP_RHS('++')}
    ))
  , ?_test(bad_prg(
      "foo : { bar : String, baz : A ~ Num } -> String\n"
      "foo(x) = x.bar\n"
      "main() = foo({ bar = \"hi\" })",
      {"{ bar : String }", "{ bar : String, baz : A ~ Num }",
       l(2, 13, 14), ?FROM_APP}
    ))


  % ensures that we don't include full lam types in errors with return values
  , ?_test(bad_prg(
      "foo : Bool\n"
      "foo = (|a, b| a + b)(1, 2)",
      {"Bool", "A ~ Num", l(1, 6, 20), ?FROM_APP}
    ))
  , ?_test(bad_prg(
      "foo : A -> Bool\n"
      "foo = (|a, b| a + b)(1)",
      {"rigid(A) -> Bool", "B ~ Num -> B ~ Num", l(1, 6, 17),
       ?FROM_APP}
    ))
  ].

global_test_() ->
  [ ?_test("A ~ Num" = ok_prg("foo = 3", "foo"))
  , ?_test("Bool -> Bool" = ok_prg(
      "f(x) =\n"
      "  let y = x && false\n"
      "  true",
      "f"
    ))
  , ?_test("[Bool]" = ok_prg(
      "foo = baz && false\n"
      "bar = [foo] ++ [true]\n"
      "baz = true",
      "bar"
    ))
  , ?_test("A ~ Num -> Float" = ok_prg(
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
      "foo : Int\n"
      "foo = bar(3)\n"
      "bar(x) = foo + x",
      "bar"
    ))


  , ?_test(bad_prg(
      "foo = \"hello\"\n"
      "expr = foo ++ @world",
      {"String", "Atom", l(1, 14, 6), ?FROM_OP_RHS('++')}
    ))
  , ?_test(bad_prg(
      "foo : Set<Int>\n"
      "foo = #[1, 2, 3]\n"
      "expr = #[5.0, 6] -- foo",
      {"Set<Float>", "Set<Int>", l(2, 20, 3), ?FROM_OP_RHS('--')}
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
  , ?_test("Foo<A ~ Num>" = ok_prg(
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
      {"([A ~ Num], Atom)", "(Float, Atom)", l(1, 11, 12), ?FROM_APP}
    ))
  , ?_test(bad_prg(
      "enum Foo<A> { Bar(A, A) }\n"
      "expr = Bar(3, true)",
      {"A ~ Num", "Bool", l(1, 14, 4), ?FROM_APP}
    ))
  , ?_test(bad_prg(
      "enum CustomList<A> { Cons(A, CustomList<A>), End }\n"
      "expr = Cons(\"hi\", Cons(5.0, End))\n",
      {"CustomList<String>", "CustomList<Float>", l(1, 18, 14), ?FROM_APP}
    ))
  ].

record_test_() ->
  % simple create/access/update record
  [ ?_test("{ bar : A ~ Num }" = ok_expr("{ bar = 3 }"))
  , ?_test("{ bar : () -> Bool }" = ok_expr("{ bar() = true }"))
  , ?_test("{ abs : A ~ Num -> A ~ Num }" = ok_expr(
      "{ abs(x) = if x > 0 then x else abs(-x) }"
    ))
  , ?_test("{ bar : A ~ Num, baz : Bool }" =
             ok_expr("{ bar = 3, baz = true }"))
  , ?_test("{ id : A -> A }" = ok_expr(
      "let id(a) = a\n"
      "{ id = id }"
    ))
  , ?_test("{ A | bar : B } -> B" = ok_expr(".bar"))
  , ?_test("Atom" = ok_expr("{ bar = @hi }.bar"))
  , ?_test("{ bar : Float }" = ok_expr("{ { bar = 3 } | bar = 4.0 }"))
  , ?_test("{ bar : Bool }" = ok_expr("{ { bar = 3 } | bar := true }"))
  , ?_test("{ bar : Bool, baz : Atom }" =
             ok_expr("{ { bar = 3, baz = @hi } | bar := true, baz = @hey }"))
  , ?_test("{ bar : Bool, baz : Float }" =
             ok_expr("{ { bar = 3, baz = @hi } | bar := true, baz := 3.0 }"))
  , ?_test(bad_expr(
      "{ abs(x) = if x > 0 then x else abs(true) }",
      {"Bool -> A ~ Num", "A ~ Num -> A ~ Num", l(2, 39), ?FROM_FIELD_DEF("abs")}
    ))
  % to ensure env is reset properly
  , ?_test(ctx_err_prg(
      "foo =\n"
      "  let f =\n"
      "    let g = true\n"
      "    1\n"
      "  g",
      {?ERR_NOT_DEF("g"), l(4, 2, 1)}
    ))
  , ?_test(bad_expr(
      "{ foo = @hi }.bar",
      {"{ foo : Atom }", "{ A | bar : B }", l(0, 17),
       ?FROM_FIELD_ACCESS("bar")}
    ))
  , ?_test(bad_expr(
      "{ { bar = 3 } | bar = true }",
      {"{ bar : A ~ Num }", "{ bar : Bool }", l(0, 28), ?FROM_RECORD_UPDATE}
    ))
  , ?_test(bad_expr(
      "{ { bar = 3, baz = @hi } | bar := true, baz = 3.0 }",
      {"{ bar : A ~ Num, baz : Atom }", "{ bar : A ~ Num, baz : Float }",
       l(0, 51), ?FROM_RECORD_UPDATE}
    ))
  , ?_test(bad_expr(
      "{ { bar = 3 } | foo = 4.0 }",
      {"{ bar : A ~ Num }", "{ B | foo : Float }", l(0, 27),
       ?FROM_RECORD_UPDATE}
    ))
  , ?_test(bad_expr(
      "{ { bar = 3 } | foo := 4.0 }",
      % record just has to contain a field foo, not necessarily of type float
      {"{ bar : A ~ Num }", "{ B | foo : C }", l(0, 28), ?FROM_RECORD_UPDATE}
    ))


  % record <=> record unification
  , ?_test("Bool" = ok_expr("{ bar = 3 } == { bar = 5 }"))
  % to avoid infinite loops from subbing anchors
  , ?_test("(Bool, Bool)" = ok_expr(
      "let x = { bar = 3 }\n"
      "let y = x\n"
      "(x == y, x == y)"
    ))
  , ?_test(bad_expr(
      "{ bar = 3 } == { bar = \"hi\" }",
      {"{ bar : A ~ Num }", "{ bar : String }", l(15, 14), ?FROM_OP_RHS('==')}
    ))
  , ?_test(bad_expr(
      "{ bar = 3 } == { foo = 4 }",
      {"{ bar : A ~ Num }", "{ foo : B ~ Num }", l(15, 11), ?FROM_OP_RHS('==')}
    ))


  % record <=> iface unification
  , ?_test("Bool" = ok_expr(
      "let f(x) = x.bar || false\n"
      "f({ bar = true })"
    ))
  , ?_test("Atom" = ok_expr(
      "let f(x) = x.bar\n"
      "f({ bar = @hi, baz = 7 })"
    ))
  , ?_test(bad_expr(
      "let f(x) = x.bar + x.baz\n"
      "f({ bar = 3 })",
      {"{ A | bar : B ~ Num, baz : B ~ Num }", "{ bar : C ~ Num }",
       l(1, 2, 11), ?FROM_APP}
    ))


  % iface <=> iface unification
  , ?_test("{ A | bar : B ~ Num, foo : String } -> (B ~ Num, String)" = ok_prg(
      "f(x) = (x.bar + 4, x.foo ++ \"hi\")",
      "f"
    ))
  , ?_test(bad_prg(
      "f(x) = (x.bar + 4, x.foo ++ \"hi\", x.foo && true)",
      {"String", "Bool", l(34, 5), ?FROM_OP_LHS('&&')}
    ))


  % occurs checks
  , ?_test(bad_expr(
      "|a| a == { bar = a }",
      {"A", "{ bar : A }", l(9, 11), ?FROM_OP_RHS('==')}
    ))
  , ?_test(bad_expr(
      "|x, a| a == { x | bar = a }",
      {"A", "{ B | bar : A }", l(12, 15), ?FROM_OP_RHS('==')}
    ))
  , ?_test(bad_expr(
      "|x, a| a == { x | bar := a }",
      {"A", "{ B | bar : A }", l(12, 16), ?FROM_OP_RHS('==')}
    ))


  % record fvs
  , ?_test(bad_prg(
      "f(x) =\n"
      "  let a() = x.a\n"
      "  (true && a(), a() ++ \"hi\")",
      {"Bool", "String", l(2, 16, 3), ?FROM_OP_LHS('++')}
    ))


  % named struct
  , ?_test("Foo" = ok_prg(
      "struct Foo { bar : Int }\n"
      "expr = Foo(3)",
      "expr"
    ))
  , ?_test("Foo" = ok_prg(
      "struct Foo { bar : Int }\n"
      "expr = Foo { bar = 3 }",
      "expr"
    ))
  , ?_test("[String] -> Foo" = ok_prg(
      "struct Foo { bar : Int, baz : [String] }\n"
      "expr = Foo(3)",
      "expr"
    ))
  , ?_test("Foo" = ok_prg(
      "struct Foo { bar : Int, baz : [Atom] }\n"
      "expr = Foo { baz = [@first, @second], bar = 15 }",
      "expr"
    ))
  , ?_test("A -> Foo<Atom, A>" = ok_prg(
      "struct Foo<X, Y> { bar : X, baz : Y }\n"
      "expr = Foo(@hi)",
      "expr"
    ))
  , ?_test("Foo<Atom>" = ok_prg(
      "struct Foo<X> { bar : X }\n"
      "expr = Foo { bar = @hi }",
      "expr"
    ))
  % Won't be able to create a valid Foo, but should still type check.
  , ?_test("Bool" = ok_prg(
      "struct Foo { baz : Foo }\n"
      "expr = true",
      "expr"
    ))
  , ?_test("Foo" = ok_prg(
      "struct Foo { bar : Atom, baz : [Foo] }\n"
      "expr = Foo { bar = @hi, baz = [Foo { bar = @hello, baz = [] }] }",
      "expr"
    ))
  , ?_test(bad_prg(
      "struct Foo { bar : (Float, Atom) }\n"
      "expr = Foo(([1], @a))",
      {"([A ~ Num], Atom)", "(Float, Atom)", l(1, 11, 9), ?FROM_APP}
    ))
  , ?_test(bad_prg(
      "struct Foo<X> { bar : [X], baz : Bool }\n"
      "expr = Foo { baz = true, bar = 5 }",
      {"{ bar : A ~ Num, baz : Bool }", "{ bar : [B], baz : Bool }",
       l(1, 7, 27), ?FROM_RECORD_CREATE("Foo")}
    ))
  , ?_test(bad_prg(
      "struct Foo<A> { bar : A, baz : A }\n"
      "expr = Foo(3, true)",
      {"A ~ Num", "Bool", l(1, 14, 4), ?FROM_APP}
    ))


  % named struct updates
  , ?_test("Foo -> Foo" = ok_prg(
      "struct Foo { bar : Int }\n"
      "f(x) = { x : Foo | bar = 7 }",
      "f"
    ))
  , ?_test("{ bar : Bool }" = ok_prg(
      "struct Foo { bar : Int }\n"
      "foo = Foo { bar = 3 }\n"
      "baz = { foo | bar := true }",
      "baz"
    ))
  , ?_test("{ bar : Bool, baz : [String] }" = ok_prg(
      "struct Foo<A> { bar : A, baz : [String] }\n"
      "foo = Foo { bar = @a, baz = [\"hi\"] }\n"
      "baz = { foo | bar := true }",
      "baz"
    ))
  , ?_test("Foo<Bool>" = ok_prg(
      "struct Foo<A> { bar : A, baz : [String] }\n"
      "foo = Foo { bar = @a, baz = [\"hi\"] }\n"
      "baz = Foo { foo | bar := true }",
      "baz"
    ))
  , ?_test(bad_prg(
      "struct Foo { bar : Int }\n"
      "foo = Foo { bar = 3 }\n"
      "baz = Foo { foo | bar := true }",
      {"{ bar : Bool }", "{ bar : Int }", l(2, 6, 25), ?FROM_RECORD_UPDATE}
    ))
  , ?_test(bad_prg(
      "struct Foo<T> { a : Map<T, String>, b : [(T, Int)] }\n"
      "foo = Foo { a = { @a => \"hi\" }, b = [(@b, 3)] }\n"
      "bar = Foo { foo | a = { true => \"hi\" } }",
      {"{ a : Map<Atom, String>, b : [(Atom, Int)] }",
       "{ a : Map<Bool, String>, b : [(Atom, Int)] }",
       l(2, 6, 34), ?FROM_RECORD_UPDATE}
    ))


  % generalization cases
  , ?_test("(String, Bool)" = ok_prg(
      "struct Foo<A> { bar : A }\n"
      "expr =\n"
      "  let id(a) = a\n"
      "  let f = Foo { bar = id }\n"
      "  (f.bar(\"hi\"), f.bar(true))",
      "expr"
    ))
  , ?_test("{ A | foo : B -> C } -> { D | bar : B } -> C" = ok_prg(
      "f(x, y) = x.foo(y.bar)",
      "f"
    ))
  , ?_test("(Bool, Bool)" = ok_expr(
      "let x = { a = 3 }\n"
      "(x == { a = 5.0 }, x == { a = 5 })"
    ))
  , ?_test(bad_prg(
      "struct Foo<A> { bar : A }\n"
      "expr = Foo(\"hi\").bar && true",
      {"String", "Bool", l(1, 7, 13), ?FROM_OP_LHS('&&')}
    ))
  , ?_test(bad_prg(
      "struct Foo<A> { bar : A }\n"
      "f(x) = (x.bar && true, x.bar ++ \"hi\")",
      {"Bool", "String", l(1, 23, 5), ?FROM_OP_LHS('++')}
    ))
  , ?_test(bad_prg(
      "f(x) = (x.bar(\"hi\"), x.bar(true))",
      {"String", "Bool", l(27, 4), ?FROM_APP}
    ))
  , ?_test(bad_prg(
      "f(x) = (x.bar(1) && true, x.bar(2, 3))",
      {"A ~ Num -> Bool", "A ~ Num -> B ~ Num -> C", l(26, 11), ?FROM_APP}
    ))
  , ?_test(bad_prg(
      "f(x) = (x.bar(2, 3), x.bar(1) && true)",
      {"A ~ Num -> B", "Bool", l(21, 8), ?FROM_OP_LHS('&&')}
    ))
  , ?_test(bad_prg(
      "f(x) =\n"
      "  let y = x.bar(2)\n"
      "  (y, g(true, x.bar))\n"
      "g(a, b) = b(a)",
      {"A ~ Num -> B", "Bool -> C", l(2, 14, 5), ?FROM_APP}
    ))
  , ?_test(bad_prg(
      "struct Foo<A> { bar : A }\n"
      "expr =\n"
      "  let id(a) = a\n"
      "  (|f| (f.bar(\"hi\"), f.bar(true)))(Foo { bar = id })",
      {"String", "Bool", l(3, 27, 4), ?FROM_APP}
    ))
  % We purposely sacrifice generalization power here in favor of safety. If
  % x unifies with Foo at any point in time, we expect that x really should be
  % of type Foo everywhere. The user can choose to override us by using the :=
  % operator to change a field's type.
  , ?_test(bad_prg(
      "struct Foo { a : Int }\n"
      "expr =\n"
      "  let x = { a = 3 }\n"
      "  (x == Foo { a = 5 }, { x | a = 3.0 })",
      {"{ a : Int }", "{ a : Float }", l(3, 23, 15), ?FROM_RECORD_UPDATE}
    ))


  % name reconciliation
  , ?_test("{ bar : A ~ Num }" = ok_prg(
      "struct Foo { bar : Int }\n"
      "expr = { bar = 3 }",
      "expr"
    ))
  , ?_test("Foo" = ok_prg(
      "struct Foo { bar : Int }\n"
      "expr =\n"
      "  let x = { bar = 3 }\n"
      "  x == Foo { bar = 4 }\n"
      "  x",
      "expr"
    ))
  , ?_test("(String, Foo<Int>)" = ok_prg(
      "struct Foo<A> { bar : A }\n"
      "expr : (String, Foo<Int>)\n"
      "expr = (\"hi\", { bar = 3 })",
      "expr"
    ))
  , ?_test("Bool" = ok_prg(
      "struct Foo { bar : Int }\n"
      "struct Baz { bar : Int }\n"
      "expr = Foo { bar = 3 } == Baz { bar = 3 }",
      "expr"
    ))
  , ?_test("Bool" = ok_prg(
      "struct Foo<A> { bar : A }\n"
      "struct Baz { bar : Int }\n"
      "expr = Foo { bar = 3 } == Baz { bar = 6 }",
      "expr"
    ))
  , ?_test("Bool" = ok_prg(
      "struct Foo<A> { bar : A, baz : String }\n"
      "struct Baz<A> { bar : Int, baz : A }\n"
      "expr = Foo { bar = 3, baz = \"hi\" } == Baz { bar = 3, baz = \"hi\" }",
      "expr"
    ))
  , ?_test(bad_prg(
      "struct Foo { bar : Int }\n"
      "expr =\n"
      "  let x = { bar = 3, baz = \"hi\" }\n"
      "  x == Foo { bar = 4 }",
      {"{ bar : A ~ Num, baz : String }", "{ bar : Int }", l(3, 7, 15),
       ?FROM_OP_RHS('==')}
    ))
  , ?_test(bad_prg(
      "struct Foo { bar : String }\n"
      "struct Baz { bar : Int }\n"
      "expr = Foo { bar = \"hi\" } == Baz { bar = 3 }",
      {"Foo", "Baz", l(2, 29, 15), ?FROM_OP_RHS('==')}
    ))
  , ?_test(bad_prg(
      "struct Foo<A> { bar : A }\n"
      "expr = { bar = true } == Foo { bar = 5 }",
      {"{ bar : Bool }", "{ bar : A ~ Num }", l(1, 25, 15),
       ?FROM_OP_RHS('==')}
    ))
  , ?_test(bad_prg(
      "struct Foo<A> { bar : A, baz : String }\n"
      "struct Baz<A> { bar : Int, baz : A }\n"
      "expr = Foo { bar = 3, baz = \"hi\" } == Baz { bar = 3, baz = true }",
      {"Foo<Int>", "Baz<Bool>", l(2, 38, 27), ?FROM_OP_RHS('==')}
    ))


  % signature cases
  , ?_test("Foo -> Int" = ok_prg(
      "struct Foo { bar : Int, baz : [String] }\n"
      "f(x) = (x : Foo).bar",
      "f"
    ))
  , ?_test("{ A | bar : String } -> String" = ok_prg(
      "f(x) = x.bar : String",
      "f"
    ))
  , ?_test("Foo -> Int" = ok_prg(
      "struct Foo { bar : Int, baz : [String] }\n"
      "f : Foo -> Int\n"
      "f(x) = x.bar + 5",
      "f"
    ))
  ].

interface_test_() ->
  [ ?_test("A ~ ToStr -> String" = ok_prg(
      "interface ToStr { to_str : T -> String }",
      "to_str"
    ))
  , ?_test("[A ~ Foo] -> A ~ Foo" = ok_prg(
      "interface Foo { foo : [T] -> T }",
      "foo"
    ))
  , ?_test("(Int, Int)" = ok_prg(
      "interface ToInt { to_int : T -> Int }\n"
      "impl ToInt for (Int, Bool) { to_int((a, _)) = a }\n"
      "impl ToInt for (Int, Bool, Int) { to_int((a, _, c)) = a + c }\n"
      "bar = (to_int((1, true)), to_int((1, false, 2)))",
      "bar"
    ))
  , ?_test("(String, String, String, String)" = ok_prg(
      "interface ToStr { to_str : T -> String }\n"
      "impl ToStr for String { to_str(s) = s }\n"
      "impl ToStr for Bool {\n"
      "  to_str(b) = if b then \"yes\" else \"no\"\n"
      "}\n"
      "impl ToStr for (A ~ ToStr, B ~ ToStr) {\n"
      "  to_str((a, b)) = \"(\" ++ to_str(a) ++ \", \" ++ to_str(b) ++ \")\"\n"
      "}\n"
      "enum Foo<A> { Foo(A) }\n"
      "impl ToStr for Foo<A ~ ToStr> {\n"
      "  to_str(Foo(a)) = \"Foo(\" ++ to_str(a) ++ \")\"\n"
      "}\n"
      "x = (\n"
      "  to_str(\"hi\"),\n"
      "  to_str((false, true)),\n"
      "  to_str(Foo(false)),\n"
      "  to_str(Foo((\"hey\", true)))\n"
      ")",
      "x"
    ))
  , ?_test(bad_prg(
      "interface Foo { foo : T -> Bool }\n"
      "impl Foo for Atom { foo(a) = @hi }",
      {"Atom -> Atom", "Atom -> Bool", l(16, 15), ?FROM_GLOBAL_SIG("foo")}
    ))
  , ?_test(bad_prg(
      "interface Foo { foo : T -> Bool }\n"
      "impl Foo for Atom { foo(a) = a == [] }",
      {"[A]", "Atom", l(1, 34, 2), ?FROM_OP_RHS('==')}
    ))
  , ?_test(bad_prg(
      "interface Foo { foo : A -> T -> A }\n"
      "impl Foo for A -> A {\n"
      "  foo(a, t) =\n"
      "    t(a)\n"
      "    a\n"
      "}",
      {"rigid(A)", "rigid(B)", l(3, 6, 1), ?FROM_APP}
    ))
  , ?_test(bad_prg(
      "interface Foo { foo : T -> Bool }\n"
      "impl Foo for Atom { foo(a) = a == @hi }\n"
      "bar = foo(\"hi\")",
      {"String", "A ~ Foo", l(2, 10, 4), ?FROM_APP}
    ))
  , ?_test(ctx_err_prg(
      "interface Foo { foo : T -> Bool }\n"
      "impl Foo for String { foo(_) = true foo(_) = false }",
      {?ERR_DUP_FIELD_IMPL("foo"), l(1, 36, 3)}
    ))
  , ?_test(ctx_err_prg(
      "interface Foo { foo : T -> Bool }\n"
      "impl Foo for String { baz(_) = \"hi\" foo(_) = false }",
      {?ERR_EXTRA_FIELD_IMPL("baz", "Foo"), l(1, 22, 3)}
    ))
  , ?_test(ctx_err_prg(
      "interface Foo { foo : T -> Bool, bar : T -> String }\n"
      "impl Foo for String { bar(_) = \"hi\" }",
      {?ERR_MISSING_FIELD_IMPL("foo", "Foo"), l(1, 0, 37)}
    ))
  , ?_test(ctx_err_prg(
      "interface Foo { foo : T -> Bool }\n"
      "impl Foo for [A] { foo(_) = true }\n"
      "impl Foo for [Int] { foo(_) = true }",
      {?ERR_DUP_IMPL("Foo", "List", "[A]"), l(2, 13, 5)}
    ))
  , ?_test(ctx_err_prg(
      "interface Foo { foo : T -> Bool }\n"
      "impl Foo for Int -> Bool { foo(_) = true }\n"
      "impl Foo for (Atom -> A) -> A { foo(_) = true }",
      {?ERR_DUP_IMPL("Foo", "function", "Int -> Bool"), l(2, 13, 16)}
    ))
  , ?_test(ctx_err_prg(
      "interface Foo { foo : Bool }",
      {?ERR_IFACE_TYPE("foo"), l(16, 10)}
    ))
  , ?_test(ctx_err_prg(
      "interface Foo { foo : T -> Int, bar : Int -> T }",
      {?ERR_IFACE_TYPE("bar"), l(32, 14)}
    ))
  , ?_test(ctx_err_prg(
      "interface Foo { foo : T, bar : T -> T }",
      {?ERR_IFACE_TYPE("foo"), l(16, 7)}
    ))


  , ?_test("Set<A ~ ToInt -> Int>" = ok_prg(
      "interface ToInt { to_int : T -> Int }\n"
      "id(a) = a\n"
      "foo =\n"
      "  let set = #[to_int]\n"
      "  id(set)",
      "foo"
    ))
  , ?_test("Bool -> A ~ ToInt -> A ~ ToInt" = ok_prg(
      "interface ToInt { to_int : T -> Int }\n"
      "foo(b, x) =\n"
      "  |y| (to_int(y), foo(b, y))\n"
      "  if b then x else foo(true, x)",
      "foo"
    ))
  % We know the impl, since it's given to foo() when x is passed. Doesn't
  % matter that we pass @io:printable_range(); the impl is the same. This
  % would *not* be the case if we provided a type signature to foo(), and
  % we'd get a must solve error (see below for test case).
  , ?_test("Bool -> A ~ ToInt -> Atom" = ok_prg(
      "interface ToInt { to_int : T -> Int }\n"
      "foo(b, x) =\n"
      "  |y| (to_int(y), foo(b, y))\n"
      "  if b then @hi else foo(true, @io:printable_range())",
      "foo"
    ))
  , ?_test(ctx_err_prg(
      "interface ToInt { to_int : T -> Int }\n"
      "impl ToInt for Int { to_int(i) = i }\n"
      "foo = to_int(@erlang:round(5.3))",
      {?ERR_MUST_SOLVE("N ~ ToInt", "N ~ ToInt"), l(2, 13, 18)}
    ))
  , ?_test(ctx_err_prg(
      "interface ToInt { to_int : T -> Int }\n"
      "impl ToInt for Int { to_int(i) = i }\n"
      "foo = to_int(3)",
      {?ERR_MUST_SOLVE("J ~ ToInt ~ Num", "J ~ ToInt ~ Num"), l(2, 13, 1)}
    ))
  , ?_test(ctx_err_prg(
      "interface ToInt { to_int : T -> Int }\n"
      "impl ToInt for Int { to_int(i) = i }\n"
      "foo = (|x| to_int(x))(@erlang:round(5.3))",
      {?ERR_MUST_SOLVE("P ~ ToInt", "P ~ ToInt"), l(2, 22, 18)}
    ))
  , ?_test(ctx_err_prg(
      "interface ToInt { to_int : T -> Int }\n"
      "impl ToInt for Int { to_int(i) = i }\n"
      "foo =\n"
      "  let to_i(x) = to_int(x)\n"
      "  to_i(3)",
      {?ERR_MUST_SOLVE("O ~ ToInt ~ Num", "O ~ ToInt ~ Num"), l(4, 7, 1)}
    ))
  , ?_test(ctx_err_prg(
      "interface ToInt { to_int : T -> Int }\n"
      "foo : Bool -> A ~ ToInt -> Atom\n"
      "foo(b, x) =\n"
      "  |y| (to_int(y), foo(b, y))\n"
      "  if b then @hi else foo(true, @io:printable_range())",
      {?ERR_MUST_SOLVE("T ~ ToInt", "T ~ ToInt"), l(4, 31, 21)}
    ))
  , ?_test(ctx_err_prg(
      "interface ToInt { to_int : T -> Int }\n"
      "foo = (|[x]| to_int(x))(@io:printable_range())",
      {?ERR_MUST_SOLVE("L ~ ToInt", "[L ~ ToInt]"), l(1, 24, 21)}
    ))


  , ?_test("(A -> B) -> C<A> ~ Mappable -> C<B> ~ Mappable" = ok_prg(
      "interface Mappable { map : (A -> B) -> T<A> -> T<B> }",
      "map"
    ))
  , ?_test("[Bool]" = ok_prg(
      "interface Mappable { map : (A -> B) -> T<A> -> T<B> }\n"
      "list_map : (A -> B) -> [A] -> [B]\n"
      "list_map = @lists:map/2\n"
      "impl Mappable for List { map = list_map }\n"
      "foo = map(|x| x == 3, [1, 2, 3])",
      "foo"
    ))
  , ?_test("Map<Atom, Char>" = ok_prg(
      "interface Mappable { map : (A -> B) -> T<A> -> T<B> }\n"
      "map_map : ((A, B) -> (C, D)) -> Map<A, B> -> Map<C, D>\n"
      "map_map(f, m) =\n"
      "  let cb = |k, v, new_m|\n"
      "    let (new_k, new_v) = f((k, v))\n"
      "    @maps:put(new_k, new_v, new_m)\n"
      "  @maps:fold(cb, {}, m)\n"
      "impl Mappable for Map { map = map_map }\n"
      "foo = map(|(k, v)| (v, k), { 'a' => @a })",
      "foo"
    ))
  , ?_test("A<(Int, Bool)> ~ Foo -> Char" = ok_prg(
      "interface Foo { foo : T<(Int, Bool)> -> Char }\n"
      "impl Foo for Map { foo(_) = 'a' }",
      "foo"
    ))
  , ?_test("Bool" = ok_prg(
      "interface Foo { foo : T -> T }\n"
      "impl Foo for Int { foo(i) = 2 * i }\n"
      "impl Foo for [A ~ Foo] {\n"
      "  foo(l) = match l { [] => l, [h | t] => [foo(h) | foo(t)] }\n"
      "}\n"
      "bar = foo(@lists:seq(1, 2) : T<Int>) == [2, 4]",
      "bar"
    ))
  , ?_test("A<B> ~ ToInt -> Int" = ok_prg(
      "interface ToInt { to_int : T -> Int }\n"
      "foo(x) =\n"
      "  @io:printable_range() : T<A> == x\n"
      "  to_int(x)",
      "foo"
    ))
  , ?_test("A<B> ~ ToInt -> Int" = ok_prg(
      "interface ToInt { to_int : T -> Int }\n"
      "foo : T<A> ~ ToInt -> Int\n"
      "foo(x) = to_int(x)",
      "foo"
    ))
  , ?_test(bad_prg(
      "interface Foo { foo : T<Int> -> Char }\n"
      "impl Foo for Map { foo(_) = 'a' }",
      {"A<Int>", "Map<B, C>", l(1, 13, 3), ?FROM_IMPL_TYPE}
    ))
  , ?_test(bad_prg(
      "interface Foo { foo : T<(Int, Bool, Char)> -> Char }\n"
      "impl Foo for Map { foo(_) = 'a' }",
      {"A<(Int, Bool, Char)>", "Map<B, C>", l(1, 13, 3), ?FROM_IMPL_TYPE}
    ))
  , ?_test(bad_prg(
      "interface ToInt { to_int : T -> Int }\n"
      "foo : T<A> -> Int\n"
      "foo(x) = to_int(x)",
      {"rigid(A)<rigid(B)>", "C ~ ToInt", l(2, 16, 1), ?FROM_APP}
    ))
  , ?_test(ctx_err_prg(
      "interface Foo { foo : T<A> -> Int }\n"
      "impl Foo for [A] { foo(_) = 3 }",
      {?ERR_IMPL_TYPE("Foo"), l(1, 13, 3)}
    ))
  , ?_test(ctx_err_prg(
      "interface Foo { foo : T<A> -> Int }\n"
      "impl Foo for Int { foo(_) = 3 }",
      {?ERR_TYPE_PARAMS("Int", 0, 1), l(1, 13, 3)}
    ))
  , ?_test(ctx_err_prg(
      "interface ToInt { to_int : T -> Int }\n"
      "foo = to_int(@io:printable_range() : T<A>)",
      {?ERR_MUST_SOLVE("R<Q> ~ ToInt", "R<Q> ~ ToInt"), l(1, 13, 28)}
    ))
  , ?_test(ctx_err_prg(
      "interface ToInt { to_int : T<A> -> Int }\n"
      "foo = to_int(@io:printable_range())",
      {?ERR_MUST_SOLVE("N ~ ToInt", "N<M> ~ ToInt"), l(1, 13, 21)}
    ))


  , ?_test("A ~ ToInt -> Int" = ok_prg(
      "interface ToInt extends Num { to_int : T -> Int }\n"
      "impl ToInt for Float { to_int(f) = @erlang:round(f) }",
      "to_int"
    ))
  , ?_test("A ~ ToInt -> B<C> ~ ToInt -> Int" = ok_prg(
      "interface ToInt extends Num { to_int : T -> Int }\n"
      "foo : A ~ ToInt ~ Num -> B<C> ~ ToInt ~ Num -> Int\n"
      "foo(a, _) = to_int(a)",
      "foo"
    ))
  , ?_test("A ~ ToInt -> B ~ Bar -> C<D> ~ Bar -> Int" = ok_prg(
      "interface ToInt {\n"
      "  to_int : T -> B ~ Foo ~ Bar -> C<D> ~ Foo ~ Bar -> Int\n"
      "}\n"
      "interface Foo { foo : T -> String }\n"
      "interface Bar extends Foo { bar : T -> Atom }",
      "to_int"
    ))
  , ?_test("A<B> ~ ToInt -> Int" = ok_prg(
      "interface Foo { foo : T<A> -> Int }\n"
      "interface ToInt extends Foo { to_int : T<A> -> Int }\n"
      "bar : A<B> ~ Foo ~ ToInt -> Int\n"
      "bar = foo\n",
      "bar"
    ))
  , ?_test("A ~ Third -> (Atom, Char, String)" = ok_prg(
      "interface First { first : T -> Atom }\n"
      "interface Second extends First { second : T -> Char }\n"
      "interface Third extends Second { third : T -> String }\n"
      "impl First for (Atom, Char, String) { first((f, _, _)) = f }\n"
      "impl Second for (Atom, Char, String) { second((_, s, _)) = s }\n"
      "impl Third for (Atom, Char, String) { third((_, _, t)) = t }\n"
      "foo(x) = (first(x), second(x), third(x))\n"
      "bar = foo((@hey, 'h', \"hello\"))",
      "foo"
    ))
  , ?_test("Int" = ok_prg(
      "interface Foo { foo : T -> String }\n"
      "interface ToInt extends Concatable, Foo { to_int : T -> Int }\n"
      "impl Foo for [A] { foo(_) = \"list\" }\n"
      "impl ToInt for [Int] {\n"
      "  to_int(l) = match l { [h | t] => h + to_int(t), [] => 0 }\n"
      "}\n"
      "bar = to_int([17, 48, 3])",
      "bar"
    ))
  , ?_test("Int" = ok_prg(
      "interface Foo { foo : T -> Int }\n"
      "interface ToInt extends Foo { to_int : T -> Int }\n"
      "impl Foo for String { foo = @erlang:byte_size/1 }\n"
      "impl Foo for [A ~ Foo] { foo([a]) = foo(a) }\n"
      "impl ToInt for String {\n"
      "  to_int(s) = foo(s) + @erlang:binary_to_integer(s)\n"
      "}\n"
      "impl ToInt for [A ~ ToInt] { to_int([a]) = to_int(a) }\n"
      "bar = to_int([\"378\"])",
      "bar"
    ))
  , ?_test("(Int, Int, [Bool], Set<{ greeting : String }>)" = ok_prg(
      "interface Collection extends Mappable { len : T<A> -> Int }\n"
      "interface Mappable { map : (A -> B) -> T<A> -> T<B> }\n"
      "impl Collection for List { len = @erlang:length/1 }\n"
      "impl Mappable for List { map = @lists:map/2 }\n"
      "impl Collection for Set { len = @gb_sets:size/1 }\n"
      "impl Mappable for Set {\n"
      "  map(f, s) = @gb_sets:fold(|e, new_s|\n"
      "    @gb_sets:add(f(e), new_s)\n"
      "  , #[], s)\n"
      "}\n"
      "foo =\n"
      "  let l = [1, 2]\n"
      "  let s = #[\"hi\"]\n"
      "  (len(l), len(s), map(|x| x == 2, l), map(|x| { greeting = x }, s))\n",
      "foo"
    ))
  , ?_test(bad_prg(
      "interface ToInt extends Num { to_int : T -> Int }\n"
      "impl ToInt for Bool { to_int(_) = 2 }",
      {"A ~ Num", "Bool", l(1, 15, 4), ?FROM_PARENT_IFACES}
    ))
  , ?_test(bad_prg(
      "interface ToInt extends Concatable, Separable { to_int : T -> Int }\n"
      "impl ToInt for String { to_int = @erlang:byte_size/1 }",
      {"A ~ Concatable ~ Separable", "String", l(1, 15, 6), ?FROM_PARENT_IFACES}
    ))
  , ?_test(bad_prg(
      "interface Foo { foo : T -> Int }\n"
      "interface ToInt extends Foo { to_int : T -> Int }\n"
      "impl Foo for [A ~ Foo] { foo([a]) = foo(a) }\n"
      "impl ToInt for [A] { to_int([a]) = 1 }",
      {"A ~ Foo", "[rigid(B)]", l(3, 15, 3), ?FROM_PARENT_IFACES}
    ))
  , ?_test(bad_prg(
      "interface Foo { foo : T -> Int }\n"
      "interface ToInt extends Foo { to_int : T -> Int }\n"
      "bar : A ~ Foo -> Int\n"
      "bar = to_int",
      {"rigid(A ~ Foo) -> Int", "B ~ ToInt -> Int", l(3, 6, 6),
       ?FROM_VAR("to_int")}
    ))
  , ?_test(ctx_err_prg(
      "interface ToInt extends Foo { to_int : T -> Int }",
      {?ERR_NOT_DEF_IFACE("Foo"), l(24, 3)}
    ))
  , ?_test(ctx_err_prg(
      "interface ToInt extends Int { to_int : T -> Int }",
      {?ERR_TYPE_NOT_IFACE("Int"), l(24, 3)}
    ))
  , ?_test(ctx_err_prg(
      "interface ToInt extends Foo { to_int : T -> Int }\n"
      "interface Foo extends ToInt { foo : T -> String }\n",
      {?ERR_CYCLE("Foo", "ToInt"), l(1, 22, 5)}
    ))
  , ?_test(ctx_err_prg(
      "interface Foo { foo : T<A> -> Int }\n"
      "interface ToInt extends Foo { to_int : T -> Int }",
      {?ERR_TYPE_PARAMS("Foo", 1, 0), l(1, 24, 3)}
    ))
  , ?_test(ctx_err_many([
      {"foo",
        "module Foo\n"
        "interface Foo { to_int : T -> Int }\n"
      },
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "interface ToInt extends Foo.Foo { to_int : T -> Int }\n"
      }
    ], "bar", {?ERR_DUP_FIELD_PARENT("to_int", "Foo"), "Bar", l(1, 34, 17)}))
  ].

gen_tv_test_() ->
  [ ?_test("([A ~ Num], Set<Atom>)" = ok_prg(
      "foo : T<A> -> T<A>\n"
      "foo(x) = x\n"
      "bar = (foo([1, 2, 3]), foo(#[@hey, @hi]))",
      "bar"
    ))
  , ?_test("[Int]" = ok_prg(
      "foo : T<Int> -> T<Int>\n"
      "foo(x) = x\n"
      "bar = foo([1])",
      "bar"
    ))
  , ?_test("([A ~ Num], Set<Atom>)" = ok_prg(
      "foo : T<A> ~ Separable -> T<A> ~ Separable\n"
      "foo(x) = x\n"
      "bar = (foo([1, 2, 3]), foo(#[@hey, @hi]))",
      "bar"
    ))
  , ?_test("A<B> ~ Concatable -> A<B> ~ Concatable -> Char" = ok_prg(
      "foo : T<A> -> T<A>\n"
      "foo(x) = x\n"
      "bar(y, z) =\n"
      "  foo(y)\n"
      "  foo(z)\n"
      "  y ++ z\n"
      "  'a'",
      "bar"
    ))
  , ?_test("[A] -> [A] -> [A]" = ok_prg(
      "foo : T<A> -> T<A>\n"
      "foo(x) = x\n"
      "bar(y, z) =\n"
      "  foo(y)\n"
      "  foo(z)\n"
      "  y ++ z\n"
      "  z ++ []",
      "bar"
    ))
  , ?_test("Map<Atom, Float>" = ok_prg(
      "foo : A -> T<A> -> T<A>\n"
      "foo(_, x) = x\n"
      "bar = foo((@hi, 3.7), { @hello => 5.1 })",
      "bar"
    ))
  , ?_test("A<B, C> -> A<B, C> -> Bool" = ok_prg(
      "foo : T<A> -> T<A>\n"
      "foo(x) = x\n"
      "bar : T<B, C> -> T<B, C>\n"
      "bar(x) = x\n"
      "baz(y, z) =\n"
      "  foo(y)\n"
      "  bar(z)\n"
      "  y == z",
      "baz"
    ))
  , ?_test("Map<Char, Bool> -> Map<Char, Bool> -> Bool" = ok_prg(
      "foo : T<A> -> T<A>\n"
      "foo(x) = x\n"
      "bar : T<B, C> -> T<B, C>\n"
      "bar(x) = x\n"
      "baz(y, z) =\n"
      "  foo(y)\n"
      "  bar(z)\n"
      "  y == z\n"
      "  z == { 'c' => true }",
      "baz"
    ))
  , ?_test(bad_prg(
      "foo : T<A> -> T<A>\n"
      "foo(x) = x\n"
      "bar = foo('c')",
      {"Char", "A<B>", l(2, 10, 3), ?FROM_APP}
    ))
  , ?_test(bad_prg(
      "foo : T<Int> -> T<Int>\n"
      "foo(x) = x\n"
      "bar = foo({})",
      {"A<Int>", "Map<B, C>", l(2, 10, 2), ?FROM_APP}
    ))
  , ?_test(bad_prg(
      "foo : T<A> -> T<A>\n"
      "foo(x) = x\n"
      "bar(y, z) =\n"
      "  foo(y)\n"
      "  foo(z)\n"
      "  y ++ z\n"
      "  z ++ \"hi\"",
      {"String", "A<B> ~ Concatable", l(6, 7, 4), ?FROM_OP_RHS('++')}
    ))
  , ?_test(bad_prg(
      "foo : T<A> ~ Num -> Float\n"
      "foo(x) = 3.7\n"
      "bar = foo([1, 2, 3])",
      {"[A ~ Num]", "B<A ~ Num> ~ Num", l(2, 10, 9), ?FROM_APP}
    ))
  , ?_test(bad_prg(
      "foo : T<A> -> T<B>\n"
      "foo(_) = @io:printable_range()\n"
      "bar(x) =\n"
      "  let y = foo(x)\n"
      "  y + 3\n"
      "  x == []",
      {"B<A> ~ Num", "[A]", l(5, 7, 2), ?FROM_OP_RHS('==')}
    ))
  , ?_test(bad_prg(
      "foo : T<A, B> -> T<A, B>\n"
      "foo(x) = x\n"
      "bar = foo([@hey])",
      {"[Atom]", "A<B, C>", l(2, 10, 6), ?FROM_APP}
    ))
  , ?_test(bad_prg(
      "foo : T<Int> -> T<Int>\n"
      "foo(x) = x\n"
      "bar : T<B, C> -> T<B, C>\n"
      "bar(x) = x\n"
      "baz(y, z) =\n"
      "  foo(y)\n"
      "  bar(z)\n"
      "  y == z",
      {"A<Int>", "B<C, D>", l(7, 7, 1), ?FROM_OP_RHS('==')}
    ))
  ].

pattern_test_() ->
  [ ?_test("Bool" = ok_expr("match 3 { 3 => true, 4.8 => false }"))
  , ?_test("Bool" = ok_expr("match -4.8 { -3 => true, -4.8 => false }"))
  , ?_test("A ~ Num" = ok_expr(
      "let x = 3\n"
      "match x + 5 { a => a + 10 }"
    ))
  , ?_test("Atom" = ok_expr("match 'x' { 'y' => @hi, 'x' => @hello }"))
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
  , ?_test("[String]" = ok_expr(
      "match [\"hi\", \"hey\"] { [] => [], [s] => [s], [_ | t] => t }"
    ))
  , ?_test("A ~ Num" = ok_expr(
      "match @io:printable_range() {\n"
      "  (a, _) => 1\n"
      "  [] => 2\n"
      "  @error => 3\n"
      "}"
    ))
  , ?_test("Float" = ok_expr(
      "let m = [([], \"hi\", 3.0), ([2, 3], \"hey\", 58.0)]\n"
      "match m {\n"
      "  [([h | t], _, _) | _] => h\n"
      "  [_, ([], _, c)] => c\n"
      "  [(_, _, c), ([x, y | []], _, _)] => c + x - y\n"
      "}"
    ))
  , ?_test("[A ~ Num]" = ok_expr(
      "let (x, y) = (3, [2])\n"
      "match [1] { &y => y ++ [1], x => x ++ [2] }"
    ))
  , ?_test("(A, B) -> A" = ok_expr("|(a, _)| a"))
  , ?_test("A ~ Num -> [B ~ Num] -> B ~ Num" = ok_prg(
      "f(3, [x | _]) = 3 + x",
      "f"
    ))
  , ?_test("Foo<A> -> [Foo<Atom>] -> Atom" = ok_prg(
      "enum Foo<A> { Bar(Atom), Baz(A) }\n"
      "f(Bar(x), [Baz(y), Baz(x) | _]) = y",
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
      "let (x, y) = (3, [2])\n"
      "match [1] { y => y ++ [1], &x => [x] }",
      {"[A ~ Num]", "B ~ Num", l(1, 27, 2), ?FROM_MATCH_PATTERN}
    ))
  , ?_test(bad_expr(
      "(|a, &a| a)(true, @hi)",
      {"Atom", "Bool", l(18, 3), ?FROM_APP}
    ))
  , ?_test(bad_expr(
      "(|[a | _], a| a)(['a'], 3.0)",
      {"Float", "Char", l(24, 3), ?FROM_APP}
    ))
  , ?_test(bad_prg(
      "enum Foo { Bar(Int), Baz(Char) }\n"
      "f(Bar(x), [Baz(y), Baz(x) | _]) = y",
      {"Int", "Char", l(1, 23, 1), ?FROM_APP}
    ))
  , ?_test(ctx_err_prg(
      "enum Foo { Bar, Baz(Int) }\n"
      "expr = match Baz(5) { Baz => 1 }",
      {?ERR_OPTION_ARITY("Baz", 1, 0), l(1, 22, 3)}
    ))
  , ?_test(ctx_err_prg(
      "enum Foo { Bar, Baz(Int) }\n"
      "expr = match Baz(5) { Baz(1, 2) => 1 }",
      {?ERR_OPTION_ARITY("Baz", 1, 2), l(1, 22, 9)}
    ))
  , ?_test(ctx_err_prg(
      "enum Foo { Bar, Baz(Int) }\n"
      "expr = match Baz(5) { Bar(2) => 1 }",
      {?ERR_OPTION_ARITY("Bar", 0, 1), l(1, 22, 6)}
    ))
  , ?_test(ctx_err_prg(
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
  , ?_test("A ~ Num" = ok_expr(
      "let [_, a] = [1, 3]\n"
      "let (&a, b, &a) = (3, 7, 3)\n"
      "b"
    ))
  , ?_test("(A, B) -> A" = ok_prg(
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
      "let [_, a] = [true, false]\n"
      "let (&a, b) = (3, 7)\n"
      "b",
      {"(Bool, A ~ Num)", "(B ~ Num, A ~ Num)", l(1, 4, 7), ?FROM_LET}
    ))
  , ?_test(bad_prg(
      "f(t) =\n"
      "  let (a, _) = t\n"
      "  a\n"
      "g(t) = f(t) : B",
      {"A", "rigid(B)", l(3, 7, 8), ?FROM_EXPR_SIG}
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

other_errors_test_() ->
  [ ?_test(ctx_err_prg(
      "foo = 3\n"
      "foo = 4",
      {?ERR_REDEF("foo"), l(1, 0, 3)}
    ))
  , ?_test(ctx_err_prg(
      "enum Foo { Bar(Int) }\n"
      "struct Bar { foo : Float }",
      {?ERR_REDEF("Bar"), l(1, 7, 3)}
    ))
  , ?_test(ctx_err_prg(
      "struct Bar<A> { foo : Float }\n"
      "enum Foo<K, V> { Bar(Int) }",
      {?ERR_REDEF("Bar"), l(1, 17, 3)}
    ))
  , ?_test(ctx_err_prg(
      "enum Int { Zero }",
      {?ERR_REDEF_BUILTIN_TYPE("Int"), l(5, 3)}
    ))
  , ?_test(ctx_err_prg(
      "enum Bool<A> { Stuff(A) }",
      {?ERR_REDEF_BUILTIN_TYPE("Bool"), l(5, 4)}
    ))
  , ?_test(ctx_err_prg(
      "interface Num { add : T -> T -> T }",
      {?ERR_REDEF_BUILTIN_IFACE("Num"), l(10, 3)}
    ))
  , ?_test(ctx_err_prg(
      "interface Separable { to_bool : T -> Bool }",
      {?ERR_REDEF_BUILTIN_IFACE("Separable"), l(10, 9)}
    ))
  , ?_test(ctx_err_prg(
      "enum Foo { Bar }\n"
      "struct Foo { baz : String }",
      {?ERR_REDEF_TYPE("Foo"), l(1, 7, 3)}
    ))
  , ?_test(ctx_err_prg(
      "struct Foo<A, B> { baz : String }\n"
      "enum Foo<T> { Bar }",
      {?ERR_REDEF_TYPE("Foo"), l(1, 5, 3)}
    ))
  , ?_test(ctx_err_prg(
      "interface Foo { baz : T -> String }\n"
      "enum Foo<T> { Bar }",
      {?ERR_REDEF_IFACE("Foo"), l(1, 5, 3)}
    ))
  , ?_test(ctx_err_prg(
      "interface Foo { baz : T -> String }\n"
      "interface Foo { bar : T -> T }",
      {?ERR_REDEF_IFACE("Foo"), l(1, 10, 3)}
    ))
  , ?_test(ctx_err_prg(
      "enum Foo<A, A> { Baz(A) }",
      {?ERR_REDEF_TV("A"), l(12, 1)}
    ))
  , ?_test(ctx_err_prg(
      "struct Foo<A, A> { baz : A }",
      {?ERR_REDEF_TV("A"), l(14, 1)}
    ))
  , ?_test(ctx_err_many([
      {"foo", "module Foo\na = 1"},
      {"bar", "module Foo\nimport \"./foo\" b = 1"}
    ], "bar", {?ERR_REDEF_MODULE("Foo"), "Foo", l(-1, 7, 3)}))
  , ?_test(ctx_err_prg(
      "foo : Int",
      {?ERR_SIG_NO_DEF("foo"), l(0, 9)}
    ))
  , ?_test(ctx_err_prg(
      "foo : Int\n"
      "bar = 3",
      {?ERR_SIG_NO_DEF("foo"), l(0, 9)}
    ))
  , ?_test(ctx_err_prg(
      "foo = 4\n"
      "foo : Int\n"
      "bar = 3",
      {?ERR_SIG_NO_DEF("foo"), l(1, 0, 9)}
    ))
  , ?_test(ctx_err_prg(
      "foo : { a : Int, a : Float }\n"
      "foo = { a = 3 }",
      {?ERR_DUP_FIELD("a"), l(17, 1)}
    ))
  , ?_test(ctx_err_prg(
      "\nfoo = { bar = 3, baz = 4, baz = \"hi\" }",
      {?ERR_DUP_FIELD("baz"), l(1, 26, 3)}
    ))
  , ?_test(ctx_err_prg(
      "\n\nfoo = Bar { baz = 4 }",
      {?ERR_NOT_DEF_TYPE("Bar"), l(2, 6, 3)}
    ))
  , ?_test(ctx_err_prg(
      "foo = Bar { { baz = 3 } | baz = 4 }",
      {?ERR_NOT_DEF_TYPE("Bar"), l(6, 3)}
    ))
  , ?_test(ctx_err_prg(
      "enum Foo {\n"
      "  Bar(\n"
      "    [\n"
      "      A\n"
      "    ]\n"
      "  )\n"
      "}",
      {?ERR_TV_SCOPE("A", "Foo"), l(3, 6, 1)}
    ))
  , ?_test(ctx_err_prg(
      "struct Foo {\n"
      "  bar :\n"
      "    [A]\n"
      "}",
      {?ERR_TV_SCOPE("A", "Foo"), l(2, 5, 1)}
    ))
  , ?_test(ctx_err_prg(
      "struct Foo<A> {\n"
      "  bar : A ~ Num\n"
      "}",
      {?ERR_TV_IFACE("A", none, gb_sets:singleton("Num")), l(1, 8, 7)}
    ))
  , ?_test(ctx_err_prg(
      "foo : A ~ Num -> A ~ Concatable\n"
      "foo(a) = @io:printable_range()",
      {
        ?ERR_TV_IFACE(
          "A",
          gb_sets:singleton("Num"),
          gb_sets:singleton("Concatable")
        ),
        l(17, 14)
      }
    ))
  , ?_test(ctx_err_prg(
      "foo : T<A> -> T\n"
      "foo(a) = @io:printable_range()",
      {?ERR_TV_NUM_PARAMS("T", 1, 0), l(14, 1)}
    ))
  , ?_test(ctx_err_prg("\n\n\nfoo = a\n", {?ERR_NOT_DEF("a"), l(3, 6, 1)}))
  , ?_test(ctx_err_prg("foo = 3 + foo", {?ERR_NOT_DEF("foo"), l(10, 3)}))
  , ?_test(ctx_err_many([
      {"foo", "module Foo a = 1"},
      {"bar", "module Bar\nimport \"./foo\"\ny = Foo.x"}
    ], "bar", {?ERR_NOT_DEF("x", "Foo"), "Bar", l(1, 4, 5)}))
  , ?_test(ctx_err_prg(
      "foo = \"hi\" : Bar",
      {?ERR_NOT_DEF_TYPE("Bar"), l(13, 3)}
    ))
  , ?_test(ctx_err_many([
      {"foo", "module Foo a = 1"},
      {"bar", "module Bar\nimport \"./foo\"\ny = 3 : Foo.FooType"}
    ], "bar", {?ERR_NOT_DEF_TYPE("FooType"), "Bar", l(1, 8, 11)}))
  , ?_test(ctx_err_prg(
      "foo = 1 : A ~ Bar",
      {?ERR_NOT_DEF_IFACE("Bar"), l(14, 3)}
    ))
  , ?_test(ctx_err_prg(
      "impl Foo for Bool { a = 3 }",
      {?ERR_NOT_DEF_IFACE("Foo"), l(5, 3)}
    ))
  , ?_test(ctx_err_many([
      {"foo", "module Foo a = 1"},
      {"bar", "module Bar\nimport \"./foo\"\ny = 3 : A ~ Foo.FooIface"}
    ], "bar", {?ERR_NOT_DEF_IFACE("FooIface"), "Bar", l(1, 12, 12)}))
  , ?_test(ctx_err_prg(
      "\nfoo = @erlang:asdf(true)",
      {?ERR_NOT_DEF_NATIVE(erlang, "asdf", 1), l(1, 6, 12)}
    ))
  , ?_test(ctx_err_prg(
      "bar = @io:format()",
      {?ERR_NOT_DEF_NATIVE(io, "format", 0), l(6, 10)}
    ))
  , ?_test(ctx_err_prg("expr = Foo.hi", {?ERR_NOT_DEF_MODULE("Foo"), l(7, 3)}))
  , ?_test(ctx_err_many([
      {"foo", "module Foo x = 3"},
      {"bar", "module Bar\nimport \"./foo\"\ny = Foo.x"}
    ], "bar", {?ERR_NOT_EXPORTED("x", "Foo"), "Bar", l(1, 4, 5)}))
  , ?_test(ctx_err_prg(
      "foo : Map<K>\n"
      "foo = {}",
      {?ERR_TYPE_PARAMS("Map", 2, 1), l(6, 6)}
    ))
  , ?_test(ctx_err_prg(
      "struct Foo<A> { bar : A }\n"
      "foo = 'a' : Foo",
      {?ERR_TYPE_PARAMS("Foo", 1, 0), l(1, 12, 3)}
    ))
  , ?_test(ctx_err_prg(
      "foo = 3 : Num",
      {?ERR_IFACE_NOT_TYPE("Num"), l(10, 3)}
    ))
  , ?_test(ctx_err_prg(
      "foo = Separable { a = 3 }",
      {?ERR_IFACE_NOT_TYPE("Separable"), l(6, 9)}
    ))
  , ?_test(ctx_err_prg(
      "interface Foo { a : T -> Int }\n"
      "foo : Foo\n"
      "foo = @hi",
      {?ERR_IFACE_NOT_TYPE("Foo"), l(1, 6, 3)}
    ))
  , ?_test(ctx_err_prg(
      "foo = 3 : A ~ Int",
      {?ERR_TYPE_NOT_IFACE("Int"), l(14, 3)}
    ))
  , ?_test(ctx_err_prg(
      "enum Bar { Bar(Int) }\n"
      "bar : A ~ Bar\n"
      "bar = Bar(3)",
      {?ERR_TYPE_NOT_IFACE("Bar"), l(1, 10, 3)}
    ))
  , ?_test(ctx_err_prg(
      "enum Foo {\n"
      "  Bar(Char)\n"
      "  Baz @Bar\n"
      "}",
      {?ERR_DUP_KEY("Bar", "Bar", l(1, 2, 3)), l(2, 6, 4)}
    ))
  , ?_test(ctx_err_prg(
      "enum Foo {\n"
      "  Bar(Char) @Baz\n"
      "  Baz\n"
      "}",
      {?ERR_DUP_KEY("Baz", "Baz", l(2, 2, 3)), l(1, 12, 4)}
    ))
  , ?_test(ctx_err_prg(
      "enum Foo {\n"
      "  Bar(Char) @hi\n"
      "  Baz @hi\n"
      "}",
      {?ERR_DUP_KEY("hi", "Bar", l(1, 12, 3)), l(2, 6, 3)}
    ))
  , ?_test(ctx_err_prg(
      "enum Foo {\n"
      "  Bar(Char)\n"
      "  Bar\n"
      "}",
      {?ERR_REDEF("Bar"), l(2, 2, 3)}
    ))
  , ?_test("Foo" = ok_prg(
      "enum Foo {\n"
      "  Bar(Char) @baz\n"
      "  Baz\n"
      "}\n"
      "expr = Bar('h')",
      "expr"
    ))

  % TODO: think about ways to improve error reporting to make this test pass
  % ensures sig constraints are unified first for better error messages
  %% , ?_test(bad_prg(
  %%     "enum Maybe<T> { Some(T), None }\n"
  %%     "struct Result<T> { a : Maybe<T> }\n"
  %%     "f : Result<T> -> Result<[T]>\n"
  %%     "f(r) = match r {\n"
  %%     "  Some(x) => { r | a := Some([x]) }\n"
  %%     "}",
  %%     {"Result<rigid(A)>", "Maybe<B>", l(4, 2, 7), ?FROM_MATCH_PATTERN}
  %%   ))
  ].

import_test_() ->
  [ ?_test("A ~ Num" = ok_many([
      {"foo", "module Foo export x = 3"},
      {"bar", "module Bar import \"./foo\" y = Foo.x + 4"}
    ], "bar", "y"))
  , ?_test("A ~ Num" = ok_many([
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
        "y = Foo.x ++ Baz.z"
      },
      {"b/baz",
        "module Baz\n"
        "import \"../foo\"\n"
        "export z = Foo.twice(@b)"
      }
    ], "a/bar", "y"))
  , ?_test("Float -> A ~ Num" = ok_many([
      {"foo",
        "module Foo\n"
        "import \"./bar\"\n"
        "export f(x) = Bar.g(x - 10.0)"
      },
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "export g(x) = if x >= 0 then 10 * Foo.f(x) else 1"
      }
    ], "foo", "f"))
  , ?_test("Baz" = ok_many([
      {"foo", "module Foo enum Baz { BazInt(Int) }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "x : Foo.Baz\n"
        "x = Foo.BazInt(3)"
      }
    ], "bar", "x"))
  , ?_test("Baz" = ok_many([
      {"foo", "module Foo struct Baz { a : Int }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "x = Foo.Baz(3)"
      }
    ], "bar", "x"))
  , ?_test("Baz" = ok_many([
      {"foo", "module Foo struct Baz { a : Int }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "x = Foo.Baz { a = 3 }"
      }
    ], "bar", "x"))
  , ?_test("Baz -> Baz" = ok_many([
      {"foo", "module Foo struct Baz { a : Int }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "f(x) = Foo.Baz { x | a = 3 }"
      }
    ], "bar", "f"))
  , ?_test("Foo" = ok_many([
      {"foo", "module Foo enum Foo { Foo(Int) }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "x : Foo.Foo\n"
        "x = Foo.Foo(3)"
      }
    ], "bar", "x"))
  , ?_test("Int" = ok_many([
      {"foo", "module Foo enum Foo { Foo(Int) }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "x = match Foo.Foo(7) { Foo.Foo(n) => n }"
      }
    ], "bar", "x"))
  , ?_test("Baz" = ok_many([
      {"foo", "module Foo struct Baz { a : Int }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "enum Baz { Baz(Foo.Baz) }\n"
        "x : Baz\n"
        "x = Baz(Foo.Baz(3))"
      }
    ], "bar", "x"))
  , ?_test(bad_many([
      {"foo",
        "module Foo\n"
        "export x = @hello"
      },
      {"bar",
       "module Bar\n"
       "import \"./foo\"\n"
       "y = Foo.x + 4"
      }
    ], "bar", {"Atom", "A ~ Num", "Bar", l(1, 4, 5), ?FROM_OP_LHS('+')}))
  , ?_test(bad_many([
      {"foo",
        "module Foo\n"
        "import \"./bar\"\n"
        "export f(x) = Bar.g(x) == 3"
      },
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "export g(x) = Foo.f(x)"
      }
    ], "foo", {"A ~ Num", "Bool", "Foo", l(1, 14, 13), ?FROM_OP_RESULT('==')}))


  , ?_test("A ~ Num" = ok_many([
      {"foo", "module Foo export x = 3"},
      {"bar", "module Bar import \"./foo\" (x) y = x + 4"}
    ], "bar", "y"))
  , ?_test("[Atom]" = ok_many([
      {"foo", "module Foo export x = [@a] export twice(x) = [x, x]"},
      {"a/bar",
        "module Bar\n"
        "import \"../foo\" (x, twice)\n"
        "y = x ++ twice(@b)"
      }
    ], "a/bar", "y"))
  , ?_test("Baz" = ok_many([
      {"foo", "module Foo struct Baz { a : Int }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\" (Baz)\n"
        "x = Baz(3)"
      }
    ], "bar", "x"))
  , ?_test("Baz" = ok_many([
      {"foo", "module Foo struct Baz { a : Int }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\" (Baz)\n"
        "x = Baz { a = 3 }\n"
        "y = Baz { { a = 3 } | a = 4 }"
      }
    ], "bar", "x"))
  , ?_test("Baz" = ok_many([
      {"foo", "module Foo enum Baz { Foo(Int) }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\" (Baz)\n"
        "x : Baz\n"
        "x = Foo.Foo(3)"
      }
    ], "bar", "x"))
  , ?_test("Foo" = ok_many([
      {"foo", "module Foo enum Foo { Foo(Int) }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\" (Foo)\n"
        "x : Foo\n"
        "x = Foo(3)"
      }
    ], "bar", "x"))
  , ?_test("Foo -> A ~ Num" = ok_many([
      {"foo", "module Foo enum Foo { One, Two(Bool), Three }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\" (One, Two, Three)\n"
        "f(x) = match x { One => 1, Two(_) => 2, Three => 3 }"
      }
    ], "bar", "f"))
  , ?_test("Foo -> A ~ Num" = ok_many([
      {"foo", "module Foo enum Foo { One, Two(Bool), Three }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\" (variants Foo)\n"
        "f(x) = match x { One => 1, Two(_) => 2, Three => 3 }"
      }
    ], "bar", "f"))
  , ?_test("Loc -> Loc" = ok_many([
      {"foo", "module Foo struct Loc { start_line : Int }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\" (Loc)\n"
        "f : Loc -> Loc\n"
        "f(l) = { start_line = l.start_line + 1 }"
      }
    ], "bar", "f"))
  , ?_test("Bar" = ok_many([
      {"foo", "module Foo struct Loc { start_line : Int }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\" (Loc)\n"
        "enum Bar { Baz(Loc) }\n"
        "x = Baz({ start_line = 3 })"
      }
    ], "bar", "x"))
  , ?_test(ctx_err_many([
      {"foo",
        "module Foo\n"
        "export x = 3"
      },
      {"bar",
        "module Bar\n"
        "import \"./foo\" (x)\n"
        "x = 4"
      }
    ], "bar", {?ERR_REDEF("x"), "Bar", l(16, 1)}))
  , ?_test(ctx_err_many([
      {"foo", "module Foo enum Foo { Foo(Int) }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\" (SomeEnum)\n"
        "x = 3"
      }
    ], "bar", {?ERR_NOT_DEF("SomeEnum", "Foo"), "Bar", l(16, 8)}))
  , ?_test(ctx_err_many([
      {"foo", "module Foo enum Foo { One, Two(Bool), Three }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\" (variants Foo)\n"
        "f : Foo -> Int\n"
        "f(x) = match x { One => 1, Two(_) => 2, Three => 3 }"
      }
    ], "bar", {?ERR_NOT_DEF_TYPE("Foo"), "Bar", l(1, 4, 3)}))
  , ?_test(ctx_err_many([
      {"foo", "module Foo export x = 3"},
      {"bar",
        "module Bar\n"
        "import \"./foo\" (x, x)\n"
        "y = x + 4"
      }
    ], "bar", {?ERR_REDEF("x"), "Bar", l(19, 1)}))
  , ?_test(ctx_err_many([
      {"foo", "module Foo enum Foo { One, Two(Bool), Three }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\" (Foo, One, variants Foo)\n"
        "f(x) = match x { One => 1, Two(_) => 2, Three => 3 }"
      }
    ], "bar", {?ERR_REDEF("One"), "Bar", l(26, 12)}))
  , ?_test(ctx_err_many([
      {"foo",
        "module Foo\n"
        "import \"./bar\"\n"
        "export x = 3"
      },
      {"bar",
        "module Bar\n"
        "import \"./baz\"\n"
        "import \"./foo\" (x)\n"
        "y = 4"
      },
      {"baz",
        "module Baz\n"
        "import \"./bar\" (x)\n"
        "z = 5"
      }
    ], "foo", {?ERR_NOT_DEF("x", "Bar"), "Baz", l(16, 1)}))


  , ?_test("Int" = ok_many([
      {"foo",
        "module Foo\n"
        "interface ToInt { to_int : T -> Int }\n"
        "impl ToInt for Char { to_int(c) = $c }\n"
        "impl ToInt for (A ~ ToInt, B ~ ToInt) {\n"
        "  to_int((a, b)) = to_int(a) + to_int(b)\n"
        "}"
      },
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "a = Foo.to_int(('a', 'b'))"
      }
    ], "bar", "a"))
  , ?_test("Int" = ok_many([
      {"foo", "module Foo interface ToInt { to_int : T -> Int }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "impl Foo.ToInt for Char { to_int(c) = $c }\n"
        "impl Foo.ToInt for (A ~ Foo.ToInt, B ~ Foo.ToInt) {\n"
        "  to_int((a, b)) = Foo.to_int(a) + Foo.to_int(b)\n"
        "}\n"
        "a = Foo.to_int(('a', 'b'))"
      }
    ], "bar", "a"))
  , ?_test("Int" = ok_many([
      {"foo",
        "module Foo\n"
        "interface ToInt { to_int : T -> Int }\n"
        "impl ToInt for Char { to_int(c) = $c }"
      },
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "impl Foo.ToInt for (A ~ Foo.ToInt, B ~ Foo.ToInt) {\n"
        "  to_int((a, b)) = Foo.to_int(a) + Foo.to_int(b)\n"
        "}\n"
        "a = Foo.to_int(('a', 'b'))"
      }
    ], "bar", "a"))
  , ?_test("Int" = ok_many([
      {"foo",
        "module Foo\n"
        "interface ToInt { to_int : T -> Int }\n"
        "impl ToInt for (A ~ ToInt, B ~ ToInt) {\n"
        "  to_int((a, b)) = to_int(a) + to_int(b)\n"
        "}"
      },
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "impl Foo.ToInt for Char { to_int(c) = $c }\n"
        "a = Foo.to_int(('a', 'b'))"
      }
    ], "bar", "a"))
  , ?_test("Int" = ok_many([
      {"foo", "module Foo interface ToInt { to_int : T -> Int }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\" (ToInt)\n"
        "impl ToInt for Char { to_int(c) = $c }\n"
        "impl ToInt for (A ~ ToInt, B ~ ToInt) {\n"
        "  to_int((a, b)) = Foo.to_int(a) + Foo.to_int(b)\n"
        "}\n"
        "a = Foo.to_int(('a', 'b'))"
      }
    ], "bar", "a"))
  , ?_test("Int" = ok_many([
      {"foo", "module Foo interface ToInt { to_int : T -> Int }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\" (ToInt, to_int)\n"
        "impl ToInt for Char { to_int(c) = $c }\n"
        "impl ToInt for (A ~ ToInt, B ~ ToInt) {\n"
        "  to_int((a, b)) = to_int(a) + to_int(b)\n"
        "}\n"
        "a = to_int(('a', 'b'))"
      }
    ], "bar", "a"))
  ].
