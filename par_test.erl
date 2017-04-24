-module(par_test).
-export([run/0]).
-include_lib("eunit/include/eunit.hrl").

-record(norm, {subs, pid}).

run() ->
  par:reload(false),

  code:soft_purge(?MODULE),
  {ok, _} = compile:file(?MODULE),
  code:load_file(?MODULE),

  ?MODULE:test().

norm_prg(Prg, Name) ->
  {ok, Env} = par:infer_prg(Prg),
  T = dict:fetch(Name, Env),

  {ok, Pid} = tv_server:start_link(),
  {NormT, _} = norm(T, #norm{subs=dict:new(), pid=Pid}),
  ok = tv_server:stop(Pid),
  NormT.

ok_prg(Prg, Name) ->
  pretty(norm_prg(Prg, Name)).

bad_prg(Prg, {EP1, EP2}) ->
  {errors, Errs} = par:infer_prg(Prg),
  [{T1, T2}] = Errs,

  {ok, Pid} = tv_server:start_link(),
  {NormT1, N} = norm(T1, #norm{subs=dict:new(), pid=Pid}),
  {NormT2, _} = norm(T2, N),

  P1 = pretty(NormT1),
  P2 = pretty(NormT2),

  case {P1, P2} of
    {EP1, EP2} -> true;
    {EP2, EP1} -> true
  end.

ok_expr(Expr) ->
  {lam, none, T} = norm_prg("main() = " ++ Expr, "main"),
  pretty(T).

bad_expr(Expr, Err) ->
  bad_prg("main() = " ++ Expr, Err).

norm({lam, ArgsT, ReturnT}, N) ->
  {NormArgsT, N1} = norm(ArgsT, N),
  {NormReturnT, N2} = norm(ReturnT, N1),
  {{lam, NormArgsT, NormReturnT}, N2};

norm({tv, V}, N) ->
  case dict:find(V, N#norm.subs) of
    {ok, NormT} -> {NormT, N};
    error ->
      NormT = tv_server:fresh(N#norm.pid),
      {NormT, N#norm{subs=dict:store(V, NormT, N#norm.subs)}}
  end;
norm({iface, I, V}, N) ->
  case dict:find(V, N#norm.subs) of
    {ok, NormT} -> {NormT, N};
    error ->
      NormT = tv_server:fresh_iface(I, N#norm.pid),
      {NormT, N#norm{subs=dict:store(V, NormT, N#norm.subs)}}
  end;

norm({con, T}, N) -> {{con, T}, N};
norm({gen, T, ParamsT}, N) ->
  {NormParamsTRev, N1} = lists:foldl(fun(P, {FoldParamsT, FoldN}) ->
    {NormP, FoldN1} = norm(P, FoldN),
    {[NormP | FoldParamsT], FoldN1}
  end, {[], N}, ParamsT),
  {{gen, T, lists:reverse(NormParamsTRev)}, N1};
norm(none, N) -> {none, N}.

pretty({lam, ArgsT, ReturnT}) ->
  Format = case ArgsT of
    {lam, _, _} -> "(~s) -> ~s";
    _ -> "~s -> ~s"
  end,
  format_str(Format, [pretty(ArgsT), pretty(ReturnT)]);
pretty({tv, TV}) -> format_str("~s", [TV]);
pretty({iface, I, TV}) -> format_str("~s: ~s", [TV, atom_to_cap_str(I)]);
pretty({con, T}) -> atom_to_cap_str(T);
pretty({gen, T, Params}) ->
  ParamsPretty = lists:map(fun(P) -> pretty(P) end, Params),
  format_str("~s<~s>", [atom_to_cap_str(T), string:join(ParamsPretty, ", ")]);
pretty(none) -> "()".

atom_to_cap_str(Atom) ->
  Str = format_str("~p", [Atom]),
  [string:to_upper(hd(Str)) | tl(Str)].

format_str(Str, Args) ->
  lists:flatten(io_lib:format(Str, Args)).

expr_test_() ->
  [ ?_test("A: Num" = ok_expr("1"))
  , ?_test("A: Num" = ok_expr("517"))
  , ?_test("Float" = ok_expr("1.0"))
  , ?_test("Float" = ok_expr("0.517"))
  , ?_test("Bool" = ok_expr("true"))
  , ?_test("Bool" = ok_expr("false"))
  , ?_test("List<Char>" = ok_expr("\"\""))
  , ?_test("List<Char>" = ok_expr("\"some string\n\""))
  , ?_test("List<A>" = ok_expr("[]"))
  , ?_test("List<A: Num>" = ok_expr("[3, 5, 6]"))
  , ?_test("List<Float>" = ok_expr("[3, 5.0, 6]"))
  , ?_test("List<Bool>" = ok_expr("[true, false, true]"))
  , ?_test(bad_expr("[3.0, true]", {"Float", "Bool"}))
  , ?_test("Tuple<Bool, Float>" = ok_expr("(true, 3.0)"))
  , ?_test("Tuple<A: Num, B: Num, List<C: Num>>" = ok_expr("(1, 2, [30, 40])"))
  , ?_test("Tuple<Tuple<A: Num, Bool>, Float>" = ok_expr("((3, false), 4.0)"))

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

  , ?_test("List<Char>" = ok_expr("\"hello \" ++ \"world\""))
  , ?_test("List<A: Num>" = ok_expr("[1, 2] ++ [3, 4, 5, 6]"))
  , ?_test("List<Bool>" = ok_expr("[] ++ [true, false]"))
  , ?_test("List<A>" = ok_expr("[] ++ []"))
  , ?_test(bad_expr("30.0 ++ \"str\"", {"Float", "List<A>"}))
  , ?_test(bad_expr("[true] ++ [1, 2]", {"Bool", "A: Num"}))

  , ?_test("A: Num" = ok_expr("-15"))
  , ?_test("Float" = ok_expr("-15.0"))
  , ?_test("Bool" = ok_expr("!false"))
  , ?_test("Bool" = ok_expr("!(-3 == 4)"))
  , ?_test(bad_expr("-true", {"Bool", "A: Num"}))
  , ?_test(bad_expr("!15.0", {"Float", "Bool"}))
  , ?_test(bad_expr("!3 == false", {"A: Num", "Bool"}))

  , ?_test("A: Num" = ok_expr("7 - (3 + -5)"))
  , ?_test("Float" = ok_expr("7 - (3.0 + -5)"))
  , ?_test("Bool" = ok_expr("7 == 5.0 || !true && -8 == 3 || false != false"))

  , ?_test("A: Num" = ok_expr("if 3 == 5 then 3 else 5"))
  , ?_test("Bool" = ok_expr("if !(true && false) then false else true"))
  , ?_test(bad_expr("if true then 3.0 else true", {"Float", "Bool"}))

  , ?_test("Float" = ok_expr("let x = 3.0 in x + 5"))
  , ?_test(bad_expr("let x = 3.0, y = true in x - y", {"Bool", "Float"}))

  , ?_test("() -> A: Num" = ok_expr("|-| 3"))
  , ?_test("A -> A" = ok_expr("|x| x"))
  , ?_test("A: Num -> A: Num" = ok_expr("|x| x + 3"))
  , ?_test("Float -> Float" = ok_expr("|x| x + 3.0"))
  , ?_test("(Float -> A) -> Float -> A" = ok_expr("|f, x| f(x - 3.0)"))
  , ?_test(bad_expr("|x| x + true", {"A: Num", "Bool"}))
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
      "f(x) = f(x) == 3 && f(x) == true\n"
      "g(x) = f(x)",
      {"A: Num", "Bool"}
    ))
  , ?_test(bad_prg(
      "f(n) = if n > 0 then f(n - 1) == 1 else true",
      {"Bool", "A: Num"}
    ))
  ].
