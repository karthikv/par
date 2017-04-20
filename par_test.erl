-module(par_test).
-export([run/0]).
-include_lib("eunit/include/eunit.hrl").

run() ->
  par:reload(false),

  code:soft_purge(?MODULE),
  {ok, _} = compile:file(?MODULE),
  code:load_file(?MODULE),

  ?MODULE:test().

ok_prg(Prg, Name) ->
  {ok, Env} = par:infer_prg(Prg),
  dict:fetch(Name, Env).

bad_prg(Prg, {T1, T2}) ->
  {errors, Errs} = par:infer_prg(Prg),
  case Errs of
    [{T1, T2}] -> true;
    [{T2, T1}] -> true
  end.

ok_expr(Expr) ->
  {lam, none, T} = ok_prg("main() = " ++ Expr, "main"),
  T.

bad_expr(Expr, Err) ->
  bad_prg("main() = " ++ Expr, Err).

expr_test_() ->
  [ ?_test({con, int} = ok_expr("1"))
  , ?_test({con, bool} = ok_expr("true"))
  , ?_test({con, bool} = ok_expr("false"))
  , ?_test({con, str} = ok_expr("\"\""))
  , ?_test({con, str} = ok_expr("\"some string\n\""))

  , ?_test({con, bool} = ok_expr("1 == 2"))
  , ?_test({con, bool} = ok_expr("1 != 2"))
  , ?_test({con, bool} = ok_expr("true == false"))
  , ?_test({con, bool} = ok_expr("true != false"))
  , ?_test(bad_expr("1 == true", {{con, int}, {con, bool}}))
  , ?_test(bad_expr("1 != true", {{con, int}, {con, bool}}))

  , ?_test({con, bool} = ok_expr("true || false"))
  , ?_test({con, bool} = ok_expr("true && false"))
  , ?_test(bad_expr("true || 1", {{con, int}, {con, bool}}))
  , ?_test(bad_expr("1 && false", {{con, int}, {con, bool}}))

  , ?_test({con, bool} = ok_expr("1 > 2"))
  , ?_test({con, bool} = ok_expr("1 < 2"))
  , ?_test({con, bool} = ok_expr("1 >= 2"))
  , ?_test({con, bool} = ok_expr("1 <= 2"))
  , ?_test(bad_expr("true > 1", {{con, bool}, {con, int}}))
  , ?_test(bad_expr("true <= 1", {{con, bool}, {con, int}}))

  , ?_test({con, int} = ok_expr("100 + 50"))
  , ?_test({con, int} = ok_expr("100 - 50"))
  , ?_test({con, int} = ok_expr("100 * 50"))
  , ?_test({con, int} = ok_expr("100 / 50"))
  , ?_test(bad_expr("true + 30", {{con, bool}, {con, int}}))
  , ?_test(bad_expr("true - 30", {{con, bool}, {con, int}}))
  , ?_test(bad_expr("30 * false", {{con, bool}, {con, int}}))
  , ?_test(bad_expr("30 / false", {{con, bool}, {con, int}}))

  , ?_test({con, str} = ok_expr("\"hello \" ++ \"world\""))
  , ?_test(bad_expr("30 ++ \"str\"", {{con, int}, {con, str}}))

  , ?_test({con, int} = ok_expr("-15"))
  , ?_test({con, bool} = ok_expr("!false"))
  , ?_test({con, bool} = ok_expr("!(-3 == 4)"))
  , ?_test(bad_expr("-true", {{con, bool}, {con, int}}))
  , ?_test(bad_expr("!15", {{con, int}, {con, bool}}))
  , ?_test(bad_expr("!3 == false", {{con, int}, {con, bool}}))

  , ?_test({con, int} = ok_expr("7 - (3 + -5)"))
  , ?_test({con, bool} = ok_expr("7 == 5 || !true && -8 == 3 || false != false"))

  , ?_test({con, int} = ok_expr("if 3 == 5 then 3 else 5"))
  , ?_test({con, bool} = ok_expr("if !(true && false) then false else true"))
  , ?_test(bad_expr("if true then 3 else true", {{con, int}, {con, bool}}))

  , ?_test({con, int} = ok_expr("let x = 3 in x + 5"))
  , ?_test(bad_expr("let x = 3, y = true in x - y", {{con, bool}, {con, int}}))

  , ?_test({lam, none, {con, int}} = ok_expr("|-| 3"))
  , ?_test({lam, {tv, A}, {tv, A}} = ok_expr("|x| x"))
  , ?_test({lam, {con, int}, {con, int}} = ok_expr("|x| x + 3"))
  , ?_test(bad_expr("|x| x + true", {{con, bool}, {con, int}}))
  ].

% TODO: prevent need to hardcode the tvs
para_poly_test_() ->
  [ ?_test({lam, {tv, A}, {tv, A}} = ok_prg("id(a) = a", "id"))
  , ?_test({lam, {lam, {con, int}, {tv, A}}, {tv, A}} =
             ok_prg("foo(f) = f(3)", "foo"))
  , ?_test({lam, {lam, {tv, B}, {tv, C}},
           {lam, {lam, {tv, A}, {tv, B}},
           {lam, {tv, A}, {tv, C}}}} = ok_prg("cmp(f, g, x) = f(g(x))", "cmp"))
  , ?_test(bad_prg("omega(x) = x(x)", {{tv, "B"}, {lam, {tv, "B"}, {tv, "C"}}}))
  ].

recur_test_() ->
  [ ?_test({lam, {tv, "B"}, {tv, "E"}} = ok_prg("f(x) = f(x)", "f"))
  , ?_test({lam, {con, int}, {con, int}} = ok_prg(
      "fib(n) = if n == 0 || n == 1 then 1 else fib(n - 1) + fib(n - 2)", "fib"
    ))
  , ?_test({lam, {con, int}, {con, int}} = ok_prg(
      "f(x) = g(x - 10)"
      "g(x) = if x >= 0 then 10 * f(x) else 1",
      "f"
    ))
  , ?_test({lam, {con, int}, {con, bool}} = ok_prg(
      "f(x) = g(x - 10) == 100"
      "g(x) = if x >= 0 && f(x) then 10 else 1",
      "f"
    ))
  , ?_test(bad_prg(
      "f(n) = if n > 0 then f(n - 1) == 1 else true",
      {{con, bool}, {con, int}}
    ))
  ].
