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
  [ ?_test({iface, num, _} = ok_expr("1"))
  , ?_test({iface, num, _} = ok_expr("517"))
  , ?_test({con, float} = ok_expr("1.0"))
  , ?_test({con, float} = ok_expr("0.517"))
  , ?_test({con, bool} = ok_expr("true"))
  , ?_test({con, bool} = ok_expr("false"))
  , ?_test({con, str} = ok_expr("\"\""))
  , ?_test({con, str} = ok_expr("\"some string\n\""))

  , ?_test({con, bool} = ok_expr("1 == 2"))
  , ?_test({con, bool} = ok_expr("1.0 == 2.0"))
  , ?_test({con, bool} = ok_expr("1.0 == 2"))
  , ?_test({con, bool} = ok_expr("1 != 2"))
  , ?_test({con, bool} = ok_expr("1.0 != 2.0"))
  , ?_test({con, bool} = ok_expr("1 != 2.0"))
  , ?_test({con, bool} = ok_expr("true == false"))
  , ?_test({con, bool} = ok_expr("true != false"))
  , ?_test(bad_expr("1 == true", {{iface, num, "B"}, {con, bool}}))
  , ?_test(bad_expr("1 != true", {{iface, num, "B"}, {con, bool}}))

  , ?_test({con, bool} = ok_expr("true || false"))
  , ?_test({con, bool} = ok_expr("true && false"))
  , ?_test(bad_expr("true || 1", {{iface, num, "B"}, {con, bool}}))
  , ?_test(bad_expr("1 && false", {{iface, num, "B"}, {con, bool}}))

  , ?_test({con, bool} = ok_expr("1 > 2"))
  , ?_test({con, bool} = ok_expr("1.2 > 2.34"))
  , ?_test({con, bool} = ok_expr("1.1 > 2"))

  , ?_test({con, bool} = ok_expr("1 < 2"))
  , ?_test({con, bool} = ok_expr("1.2 < 2.34"))
  , ?_test({con, bool} = ok_expr("1 < 2.34"))

  , ?_test({con, bool} = ok_expr("1 >= 2"))
  , ?_test({con, bool} = ok_expr("1.2 >= 2.34"))
  , ?_test({con, bool} = ok_expr("1.1 >= 2"))

  , ?_test({con, bool} = ok_expr("1 <= 2"))
  , ?_test({con, bool} = ok_expr("1.2 <= 2.34"))
  , ?_test({con, bool} = ok_expr("1 <= 2.34"))

  , ?_test(bad_expr("true > 1", {{con, bool}, {iface, num, "D"}}))
  , ?_test(bad_expr("true <= 1", {{con, bool}, {iface, num, "D"}}))

  , ?_test({iface, num, _} = ok_expr("100 + 50"))
  , ?_test({con, float} = ok_expr("100.1 + 50.23"))
  , ?_test({con, float} = ok_expr("100 + 50.23"))

  , ?_test({iface, num, _} = ok_expr("100 - 50"))
  , ?_test({con, float} = ok_expr("100.1 - 50.23"))
  , ?_test({con, float} = ok_expr("100.1 - 50"))

  , ?_test({iface, num, _} = ok_expr("100 * 50"))
  , ?_test({con, float} = ok_expr("100.1 * 50.23"))
  , ?_test({con, float} = ok_expr("100.1 * 50"))

  , ?_test({con, float} = ok_expr("100 / 50"))
  , ?_test({con, float} = ok_expr("100.1 / 50.23"))
  , ?_test({con, float} = ok_expr("100.1 / 50"))

  , ?_test(bad_expr("true + 30", {{con, bool}, {iface, num, "D"}}))
  , ?_test(bad_expr("true - 30.0", {{con, bool}, {iface, num, "C"}}))
  , ?_test(bad_expr("30 * false", {{con, bool}, {iface, num, "D"}}))
  , ?_test(bad_expr("30 / false", {{con, bool}, {iface, num, "D"}}))

  , ?_test({con, str} = ok_expr("\"hello \" ++ \"world\""))
  , ?_test(bad_expr("30.0 ++ \"str\"", {{con, float}, {con, str}}))

  , ?_test({iface, num, _} = ok_expr("-15"))
  , ?_test({con, float} = ok_expr("-15.0"))
  , ?_test({con, bool} = ok_expr("!false"))
  , ?_test({con, bool} = ok_expr("!(-3 == 4)"))
  , ?_test(bad_expr("-true", {{con, bool}, {iface, num, "C"}}))
  , ?_test(bad_expr("!15.0", {{con, float}, {con, bool}}))
  , ?_test(bad_expr("!3 == false", {{iface, num, "B"}, {con, bool}}))

  , ?_test({iface, num, _} = ok_expr("7 - (3 + -5)"))
  , ?_test({con, float} = ok_expr("7 - (3.0 + -5)"))
  , ?_test({con, bool} = ok_expr("7 == 5.0 || !true && -8 == 3 || false != false"))

  , ?_test({iface, num, _} = ok_expr("if 3 == 5 then 3 else 5"))
  , ?_test({con, bool} = ok_expr("if !(true && false) then false else true"))
  , ?_test(bad_expr("if true then 3.0 else true", {{con, float}, {con, bool}}))

  , ?_test({con, float} = ok_expr("let x = 3.0 in x + 5"))
  , ?_test(bad_expr("let x = 3.0, y = true in x - y", {{con, bool}, {con, float}}))

  , ?_test({lam, none, {iface, num, _}} = ok_expr("|-| 3"))
  , ?_test({lam, {tv, A}, {tv, A}} = ok_expr("|x| x"))
  , ?_test({lam, {iface, num, _}, {iface, num, _}} =
             ok_expr("|x| x + 3"))
  , ?_test({lam, {con, float}, {con, float}} = ok_expr("|x| x + 3.0"))
  , ?_test({lam, {lam, {con, float}, {tv, A}}, {lam, {con, float}, {tv, A}}} =
             ok_expr("|f, x| f(x - 3.0)"))
  , ?_test(bad_expr("|x| x + true", {{con, bool}, {iface, num, "D"}}))
  ].

% TODO: prevent need to hardcode the tvs
para_poly_test_() ->
  [ ?_test({lam, {tv, A}, {tv, A}} = ok_prg("id(a) = a", "id"))
  , ?_test({lam, {lam, {iface, num, _}, {tv, A}}, {tv, A}} =
             ok_prg("foo(f) = f(3)", "foo"))
  , ?_test({lam, {lam, {tv, B}, {tv, C}},
           {lam, {lam, {tv, A}, {tv, B}},
           {lam, {tv, A}, {tv, C}}}} = ok_prg("cmp(f, g, x) = f(g(x))", "cmp"))
  , ?_test(bad_prg("omega(x) = x(x)", {{tv, "B"}, {lam, {tv, "B"}, {tv, "C"}}}))
  ].

recur_test_() ->
  [ ?_test({lam, {tv, "B"}, {tv, "C"}} = ok_prg("f(x) = f(x)", "f"))
  , ?_test({lam, {iface, num, _}, {iface, num, _}} = ok_prg(
      "fib(n) = if n == 0 || n == 1 then 1 else fib(n - 1) + fib(n - 2)", "fib"
    ))
  , ?_test({lam, {con, float}, {iface, num, "N"}} = ok_prg(
      "f(x) = g(x - 10.0)\n"
      "g(x) = if x >= 0 then 10 * f(x) else 1",
      "f"
    ))
  , ?_test({lam, {iface, num, _}, {con, bool}} = ok_prg(
      "f(x) = g(x - 10) == 100\n"
      "g(x) = if x >= 0 && f(x) then 10 else 1",
      "f"
    ))
  , ?_test(bad_prg(
      "f(x) = f(x) == 3 && f(x) == true\n"
      "g(x) = f(x)",
      {{iface, num, "E"}, {con, bool}}
    ))
  , ?_test(bad_prg(
      "f(n) = if n > 0 then f(n - 1) == 1 else true",
      {{con, bool}, {iface, num, "J"}}
    ))
  ].
