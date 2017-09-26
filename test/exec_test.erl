-module(exec_test).
-export([returns_fun/0]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/common.hrl").

-define(TMP_MANY_DIR, "/tmp/exec-test-many").

run_code_gen(Prg) ->
  {ok, Comps, C} = type_system_test:type_check(Prg),
  [{Mod, Binary}] = code_gen:compile_comps(Comps, C),

  remove(Mod),
  code:load_binary(Mod, "", Binary),

  Mod:'_@init'(gb_sets:new()),
  Mod:main().

run_interpreter(Prg) ->
  {ok, [#comp{ast=Ast}], _} = type_system_test:type_check(Prg),
  interpreter:run_ast(Ast, []).

expr_code_gen(Expr) -> run_code_gen("main() = " ++ Expr).
expr_interpreter(Expr) -> run_interpreter("main() = " ++ Expr).

many_code_gen(PathPrgs, TargetPath) ->
  {ok, Comps, C} = type_system_test:type_check_many(
    ?TMP_MANY_DIR,
    PathPrgs,
    TargetPath
  ),

  code:add_patha(?TMP_MANY_DIR),
  lists:foreach(fun({Mod, Binary}) ->
    Path = filename:join(?TMP_MANY_DIR, lists:concat([Mod, ".beam"])),
    file:write_file(Path, Binary),
    remove(Mod)
  end, code_gen:compile_comps(Comps, C)),

  #comp{module=Module} = hd(Comps),
  Mod = list_to_atom(Module),
  Mod:'_@init'(gb_sets:new()),

  V = Mod:main(),
  code:del_path(?TMP_MANY_DIR),
  V.

remove(Mod) ->
  code:purge(Mod),
  code:delete(Mod),
  code:purge(Mod).

code_gen_expr_test_() -> test_expr(fun expr_code_gen/1).
interpreter_expr_test_() -> test_expr(fun expr_interpreter/1).
test_expr(Expr) ->
  [ ?_test({} = Expr("()"))
  , ?_test(1 = Expr("1"))
  , ?_test(3.0 = Expr("3.0"))
  , ?_test(true = Expr("true"))
  , ?_test($h = Expr("'h'"))
  , ?_test($\n = Expr("'\\n'"))
  , ?_test(<<"hi">> = Expr("\"hi\""))
  , ?_test(<<"hi\n">> = Expr("\"hi\\n\""))
  , ?_test(hi = Expr("@hi"))
  , ?_test('hello world' = Expr("@\"hello world\""))
  , ?_test([3.0, 5] = Expr("[3.0, 5]"))
  , ?_test({<<"what">>, false, 7} = Expr("(\"what\", false, 7)"))
  , ?_assertEqual(#{}, Expr("{}"))
  , ?_assertEqual(
      #{<<"hello">> => <<"world">>, <<"some">> => <<"thing">>},
      Expr("{\"hello\" => \"world\", \"some\" => \"thing\"}")
    )
  , ?_assertEqual(gb_sets:new(), Expr("#[]"))
  , ?_assertEqual(
      gb_sets:from_list([2, 4, 6, 8]),
      Expr("#[2, 4, 2, 6, 4, 8, 6]")
    )


  , ?_test({3.0, true} = (Expr("|x| x"))({3.0, true}))
  , ?_test(35.0 = (Expr("|x, y| x * y * 3.5"))(4, 2.5))
  , ?_test(true = Expr("(|x| x || true)(false)"))
  , ?_test(<<"ab">> = Expr("(|a, b| a ++ b)(\"a\")(\"b\")"))
  , ?_test(5 = Expr("(|x| |y| x + y)(2, 3)"))
  , ?_test([4, 1] = Expr("(|x| |-| x -- [3])([4, 3, 1])()"))
  % to test code_gen_utils:'_@curry' in the parital application case
  , ?_test(2 = Expr(
      "let f = (|a| |b, c, d| a - b + c - d)(4), f = f(3) in f(2, 1)"
    ))


  , ?_test(<<"world">> = Expr("if false then \"hello\" else \"world\""))
  , ?_test([true, false] =
             Expr("if false || true && 3.5 < 4 then [true, false] else [true]"))
  , ?_test({} = Expr("if true then @foo"))
  , ?_test({} = Expr("if false then @io:nl() : () else discard 3"))
  % ensures that we handle conditions that aren't valid guard clauses
  , ?_test($a = Expr("let f = |x| x == 3 in if f(3) then 'a' else 'b'"))

  , ?_test(5 = Expr("let x = 5 in x"))
  % ensures that we generate a unique name for each variable; otherwise, we'll
  % get a badmatch 4 <=> 5
  , ?_test(5 = Expr("let x = (let x = 4, y = 5 in y) in x"))
  , ?_test(true = Expr("let x = 5, y = true in x == 4 || y"))
  , ?_test(false =
             Expr("let and = |a, b, c| a && b && c in and(true, true, false)"))
  , ?_test([4, 3, 4, 2, 3] =
             Expr("let a = [4], f(x) = a ++ x ++ [3] in f([]) ++ f([2])"))
  , ?_test(15 = Expr("let a = 10, b = a + 5 in b"))
  , ?_test(32 = Expr(
      "let f = |x, c| if x == 0 then c else f(x - 1, c * 2) in\n"
      "  f(5, 1)"
    ))
  , ?_test(true = Expr("let a = 1, a = a == 1 in a"))


  , ?_test(<<"hello">> = Expr("{ \"hello\" }"))
  , ?_test(true = Expr("{ @foo; true }"))
  , ?_assertEqual(
      #{<<"hi">> => 5},
      Expr("let x = 5 in { @erlang:hd([1]); 3.0; {\"hi\" => x} }")
    )

  , ?_test(false = Expr("1 == 2"))
  , ?_test(true = Expr("(3, 4) == (3, 4)"))
  , ?_test(false = Expr("5.0 != 5.0"))
  , ?_test(true = Expr("true != false"))
  , ?_test(true = Expr("false || true"))
  , ?_test(false = Expr("false || false"))
  , ?_test(true = Expr("true && true"))
  , ?_test(false = Expr("false && true"))
  % short circuiting
  , ?_test(false = Expr("false && @erlang:hd([])"))
  , ?_test(true = Expr("true || @erlang:hd([])"))
  , ?_test(true = Expr("3.0 > 2"))
  , ?_test(false = Expr("5 > 7"))
  , ?_test(true = Expr("1.3 < 1.4"))
  , ?_test(false = Expr("15 < 14"))
  , ?_test(true = Expr("3.0 >= 3.0"))
  , ?_test(false = Expr("2 >= 3"))
  , ?_test(true = Expr("12 <= 12"))
  , ?_test(false = Expr("27 <= 26"))
  , ?_test(3 = Expr("1 + 2"))
  , ?_test(4.2 = Expr("1.5 + 2.7"))
  , ?_test(-3 = Expr("7 - 10"))
  , ?_test(0.5 = Expr("1.5 - 1"))
  , ?_test(854 = Expr("14 * 61"))
  , ?_test(37.12 = Expr("6.4 * 5.8"))
  , ?_test(1.57 = Expr("48.67 / 31"))
  , ?_test(17.0 = Expr("85 / 5"))
  , ?_test(2 = Expr("17 % 3"))
  , ?_test(-3 = Expr("-7 % 4"))
  , ?_test(30.0 = Expr("3 + 5 * 7 - 4 / 2 + 38 % 6 - 8"))
  , ?_test([$a] = Expr("['a' | []]"))
  , ?_test([a, b, c] = Expr("[@a | [@b, @c]]"))
  , ?_test([3, 4, 5] = Expr("[3, 4 | [5]]"))
  , ?_test([[]] = Expr("[[] | []]"))
  , ?_test([1, 2, 3, 4] = Expr("[1] ++ [2, 3, 4]"))
  , ?_test(<<"hello world">> = Expr("\"hello \" ++ \"world\""))
  , ?_assertEqual(
      #{<<"a">> => 1, <<"b">> => 2.0},
      Expr("{\"a\" => 1} ++ {\"b\" => 2.0}")
    )
  , ?_assertEqual(
      gb_sets:from_list([1, 2, 3]),
      Expr("#[1] ++ #[2, 3]")
    )
  , ?_assertEqual(
      [3, 8],
      Expr("[5, 3, 1, 4, 5, 8, 7] -- [4, 1, 5, 7]")
    )
  , ?_assertEqual(
      gb_sets:from_list([3]),
      Expr("#[3, 2, 3, 1, 2] -- #[1, 8, 6, 2]")
    )
  , ?_test(-3 = Expr("-3"))
  , ?_test(-78.5 = Expr("-5 * 15.7"))
  , ?_test(false = Expr("!true"))
  , ?_test(true = Expr("!false && true"))
  , ?_test($h = Expr("$'h'"))


  , ?_test([4, 6] = Expr("@lists:filter(|x| x > 3, [2, 4, 6])"))
  , ?_test([6] = Expr("@lists:filter((|t, x| x > t)(5), [2, 4, 6])"))
  , ?_test([true] = Expr("@lists:map(@erlang:is_atom/1, [@a])"))
  , ?_test(3 = Expr("@exec_test:returns_fun()(1)(2)"))
  , ?_test(3 = Expr("@exec_test:returns_fun/0((), 1)(2)"))
  , ?_test(3 = Expr("@exec_test:returns_fun/0((), 1, 2)"))
  , ?_test(true = Expr("let foo(x) = x == () in foo()"))
  , ?_test(true = Expr("let foo(x) = x == () in foo(())"))

  , ?_test(<<"hello world">> = Expr("\"hello\" |> |x| x ++ \" world\""))
  , ?_test(77 = Expr("let inc(x) = x + 1 in (5 |> |x| 2 * x |> inc) * 7"))
  , ?_test(true = (Expr("let f(x, y) = x == y in @hi |> f"))(hi))
  ].

% used for the last few tests above
returns_fun() ->
  fun(A, B) -> A + B end.

code_gen_prg_test_() -> test_prg(fun run_code_gen/1).
interpreter_prg_test_() -> test_prg(fun run_interpreter/1).
test_prg(Run) ->
  [ ?_test(3 = Run(
     "main : () -> Int\n"
     "main() = 3 : Int"
    ))
  , ?_test(8 = Run(
      "fib(n) = if n == 0 || n == 1 then n else fib(n - 1) + fib(n - 2)\n"
      "main() = fib(6)"
    ))
  , ?_test([false, false, true] = Run(
      "cmp(f, g, x) = f(g(x))\n"
      "two(e) = [e, e]\n"
      "and_true(l) = l ++ [true]\n"
      "main() = cmp(and_true)(two, false)"
    ))
  , ?_test(50 = Run(
      "f(x) = g(x - 10.0)\n"
      "g(x) = if x >= 0 then 10 + f(x) else 0\n"
      "main() = f(57)"
    ))
  ].

code_gen_global_test_() -> test_global(fun run_code_gen/1).
interpreter_global_test_() -> test_global(fun run_interpreter/1).
test_global(Run) ->
  [ ?_test(3 = Run(
      "foo = 3\n"
      "main() = foo"
    ))
  , ?_test([false, true] = Run(
      "foo = baz && false\n"
      "bar = [foo] ++ [true]\n"
      "baz = true\n"
      "main() = bar"
    ))
  , ?_test(7812.5 = Run(
      "foo = |x| bar(x) / 2\n"
      "bar(x) = if x == 0 then 1 else foo(x - 1) * 10\n"
      "main() = foo(6)"
    ))
  % to ensure no warnings from arg shadowing b/c of currying
  , ?_test({{<<"hi">>, $d}, 3, 4} = Run(
      "bar(a, b, c) = (a('d'), b, c)\n"
      "baz(a, b) = (a, b)\n"
      "foo = bar(baz(\"hi\"))\n"
      "main() = foo(3, 4)"
    ))
  % to ensure globals are evaluated strictly in order
  , ?_test("hi" = Run(
      "foo = to_list(\"hi\")\n"
      "to_list = @erlang:binary_to_list/1\n"
      "main() = foo"
    ))
  % to ensure globals are only evaluated once
  , ?_test({ok, <<"bar">>} = Run(
      "foo = @file:write_file(\"/tmp/par-foo\", \"bar\")\n"
      "bar = let result = @file:read_file(\"/tmp/par-foo\") in\n"
      "  { @file:delete(\"/tmp/par-foo\"); result }"
      "main() = bar"
    ))
  % to ensure indirect global dependencies (foo -> f -> b) work
  , ?_test(8 = Run(
      "foo = f(3)\n"
      "f(x) = x + bar\n"
      "bar = 5\n"
      "main() = foo"
    ))
  ].

code_gen_enum_test_() -> test_enum(fun run_code_gen/1).
interpreter_enum_test_() -> test_enum(fun run_interpreter/1).
test_enum(Run) ->
  [ ?_test('Bar' = Run(
      "enum Foo { Bar }\n"
      "main() = Bar"
    ))
  , ?_test({'Other', 5} = Run(
      "enum Foo { Bar, Other(Int) }\n"
      "main() = Other(5)"
    ))
  , ?_test({'Bar', true, [<<"hello">>]} = (Run(
      "enum Foo { Bar(Bool, [String]) }\n"
      "main() = Bar(true)"
    ))([<<"hello">>]))
  , ?_test('Bar' = Run(
      "enum Foo<A> { Bar }\n"
      "main() = Bar"
    ))
  , ?_test({'Other', 3} = Run(
      "enum Foo<A> { Bar, Other(A) }\n"
      "main() = Other(3)"
    ))
  , ?_test({'Cons', 3, {'Cons', 5.0, 'End'}} = Run(
      "enum CustomList<A> { Cons(A, CustomList<A>), End }\n"
      "main() = Cons(3, Cons(5.0, End))\n"
    ))
  , ?_test(error = Run(
      "enum Result { Err @error }\n"
      "main() = Err"
    ))
  , ?_test({ok, 5} = Run(
      "enum Result<T> { Ok(T) @ok }\n"
      "main() = Ok(5)"
    ))
  , ?_test({'==', true, <<"hi">>} = Run(
      "enum Expr { Eq(Bool, String) @\"==\" }\n"
      "main() = Eq(true, \"hi\")"
    ))
  ].

code_gen_record_test_() ->
  test_record(fun expr_code_gen/1, fun run_code_gen/1).
interpreter_record_test_() ->
  test_record(fun expr_interpreter/1, fun run_interpreter/1).
test_record(Expr, Run) ->
  [ ?_assertEqual(#{bar => 3}, Expr("{ bar = 3 }"))
  , ?_assertEqual(
      #{bar => 3, baz => true},
      Expr("{ bar = 3, baz = true }")
    )
  , ?_test(8 = Expr("{ bar = |x| x + 5 }.bar(3)"))
  , ?_test(5 = Expr("{ abs(x) = if x > 0 then x else abs(-x) }.abs(-5)"))
  , ?_assertEqual(#{bar => 4.0}, Expr("{ { bar = 3 } | bar = 4.0 }"))
  , ?_assertEqual(#{bar => true}, Expr("{ { bar = 3 } | bar := true }"))
  , ?_assertEqual(#{bar => true, baz => hey}, Expr(
      "{ { bar = 3, baz = @hi } | bar := true, baz = @hey }"
    ))
  , ?_assertEqual(#{bar => true, baz => 3.0}, Expr(
      "{ { bar = 3, baz = @hi } | bar := true, baz := 3.0 }"
    ))

  , ?_test(false = Expr("{ bar = 3 } == { bar = 5 }"))
  , ?_test(true = Expr("{ bar = 3 } == { bar = 3 }"))


  , ?_test(true = Expr("let f(x) = x.bar || false in f({ bar = true })"))
  , ?_test(hi = Expr("let f(x) = x.bar in f({ bar = @hi, baz = 7 })"))

  , ?_test({11, <<"oh, hi">>} = Run(
      "f(x) = (x.bar + 4, x.foo ++ \"hi\")\n"
      "main() = f({ bar = 7, foo = \"oh, \" })"
    ))

  % named struct
  , ?_assertEqual(#{bar => 3}, Run(
      "struct Foo { bar : Int }\n"
      "main() = Foo(3)"
    ))
  , ?_assertEqual(#{bar => 3}, Run(
      "struct Foo { bar : Int }\n"
      "main() = Foo { bar = 3 }"
    ))
  , ?_assertEqual(#{bar => 3, baz => [<<"hello">>]}, (Run(
      "struct Foo { bar : Int, baz : [String] }\n"
      "main() = Foo(3)"
    ))([<<"hello">>]))
  , ?_assertEqual(#{baz => [first, second], bar => 15}, Run(
      "struct Foo { bar : Int, baz : [Atom] }\n"
      "main() = Foo { baz = [@first, @second], bar = 15 }"
    ))
  , ?_assertEqual(#{bar => hi, baz => true}, (Run(
      "struct Foo<X, Y> { bar : X, baz : Y }\n"
      "main() = Foo(@hi)"
    ))(true))
  , ?_assertEqual(#{bar => hi}, Run(
      "struct Foo<X> { bar : X }\n"
      "main() = Foo { bar = @hi }"
    ))
  % Won't be able to create a valid Foo, but should still type check.
  , ?_test(true = Run(
      "struct Foo { baz : Foo }\n"
      "main() = true"
    ))
  , ?_assertEqual(
      #{bar => hi, baz => [#{bar => hello, baz => []}]},
      Run(
        "struct Foo { bar : Atom, baz : [Foo] }\n"
        "main() = Foo { bar = @hi, baz = [Foo { bar = @hello, baz = [] }] }"
      )
    )


  % named struct updates
  , ?_assertEqual(#{bar => 7}, Run(
      "struct Foo { bar : Int }\n"
      "f(x) = { x : Foo | bar = 7 }\n"
      "main() = f({ bar = 3 })"
    ))
  , ?_assertEqual(#{bar => true}, Run(
      "struct Foo { bar : Int }\n"
      "foo = Foo { bar = 3 }\n"
      "main() = { foo | bar := true }"
    ))
  , ?_assertEqual(#{bar => true, baz => [<<"hi">>]}, Run(
      "struct Foo<A> { bar : A, baz : [String] }\n"
      "foo = Foo { bar = @a, baz = [\"hi\"] }\n"
      "main() = { foo | bar := true }"
    ))
  , ?_assertEqual(#{bar => true, baz => [<<"hi">>]}, Run(
      "struct Foo<A> { bar : A, baz : [String] }\n"
      "foo = Foo { bar = @a, baz = [\"hi\"] }\n"
      "main() = Foo { foo | bar := true }"
    ))


  % generalization cases
  , ?_test({<<"hi">>, true} = Run(
      "struct Foo<A> { bar : A }\n"
      "main() = let id(a) = a, f = Foo { bar = id } in\n"
      "  (f.bar(\"hi\"), f.bar(true))"
    ))
  , ?_test(7.5 = Run(
      "f(x, y) = x.foo(y.bar)\n"
      "main() = f({ foo = |x| x.baz }, { bar = { baz = 7.5 } })"
    ))
  ].

code_gen_interface_test_() -> test_interface(fun run_code_gen/1).
%% interpreter_interface_test_() -> test_interface(fun run_interpreter/1).
test_interface(Run) ->
  [ ?_test(1 = Run(
      "interface ToInt { to_int : T -> Int }\n"
      "impl ToInt for Bool {\n"
      "  to_int(b) = if b then 1 else 0\n"
      "}\n"
      "main() = to_int(true)"
    ))
  , ?_test(1 = Run(
      "interface ToInt { to_int : T -> Int }\n"
      "impl ToInt for Bool {\n"
      "  to_int(b) = if b then 1 else 0\n"
      "}\n"
      "main() = (to_int : Bool -> Int)(true)"
    ))
  , ?_test(1 = Run(
      "interface ToInt { to_int : T -> Int }\n"
      "impl ToInt for Bool {\n"
      "  to_int(b) = if b then 1 else 0\n"
      "}\n"
      "main() = (to_int : T ~ ToInt -> Int)(true)"
    ))
  , ?_test(0 = Run(
      "interface ToInt { to_int : T -> Int }\n"
      "impl ToInt for Bool {\n"
      "  to_int(b) = if b then 1 else 0\n"
      "}\n"
      "proxy(b) = to_int(b)\n"
      "main() = proxy(false)"
    ))
  % to ensure no impl arg is added to lambda |c| ... because of bound impl b
  , ?_test(1 = Run(
      "interface ToInt { to_int : T -> Int }\n"
      "impl ToInt for Bool {\n"
      "  to_int(b) = if b then 1 else 0\n"
      "}\n"
      "foo(b) = |c| if b == c then to_int(c) else -1\n"
      "main() = foo(true, true)"
    ))
  % to test fns with multiple arguments having the same iv pair
  , ?_test(7 = Run(
      "interface ToInt { to_int : T -> Int }\n"
      "impl ToInt for Float {\n"
      "  to_int(n) = @erlang:round(n)\n"
      "}\n"
      "foo(a, b) = if a == b then to_int(a) * 2 else to_int(a) + to_int(b)\n"
      "main() = foo(3.7, 3.1)"
    ))
  % to test recursive fns that we can't inst
  , ?_test(2 = Run(
      "interface ToInt { to_int : T -> Int }\n"
      "impl ToInt for Bool {\n"
      "  to_int(b) = if b then 1 else 0\n"
      "}\n"
      "foo(twice, b) = if twice then 2 * foo(false, b) else to_int(b)\n"
      "main() = foo(true, true)"
    ))
  % this time, a fn that's both recursive and with bound variables
  , ?_test(4 = Run(
      "interface ToInt { to_int : T -> Int }\n"
      "impl ToInt for Bool {\n"
      "  to_int(b) = if b then 1 else 0\n"
      "}\n"
      "foo(t, b) =\n"
      "  let bar(twice, c) =\n"
      "    if twice then\n"
      "      2 * bar(false, c)\n"
      "    else if b == c then\n"
      "      2 * to_int(c)\n"
      "    else\n"
      "      to_int(c)\n"
      "  in bar(t, b)\n"
      "main() = foo(true, true)"
    ))
  , ?_test({2, 3} = Run(
      "interface ToInt { to_int : T -> Int }\n"
      "impl ToInt for [A] { to_int(l) = @erlang:length(l) }\n"
      "interface Foo { foo : T -> (T, A ~ ToInt) -> Int }\n"
      "impl Foo for Bool {\n"
      "  foo(a, (b, c)) = if b && a then 2 * to_int(c) else to_int(c)\n"
      "}\n"
      "main() = (foo(true, (true, [1])), foo(false, (true, ['a', 'b', 'c'])))"
    ))
  , ?_test({1, 2} = Run(
      "interface ToInt { to_int : T -> Int }\n"
      "impl ToInt for [A] { to_int(l) = @erlang:length(l) }\n"
      "interface Foo { foo : T -> (T, A ~ ToInt) -> Int }\n"
      "impl Foo for Bool {\n"
      "  foo(a, (b, c)) = if b && a then 2 * to_int(c) else to_int(c)\n"
      "}\n"
      "main() = (\n"
      "  (foo : T ~ Foo -> (T ~ Foo, [Int]) -> Int)(true, (false, [1])),\n"
      "  (foo : Bool -> (Bool, A ~ ToInt) -> Int)(false, (false, [@a, @b]))\n"
      ")"
    ))
  , ?_test({{ok, <<"combine">>}, false} = Run(
      "filename = \"/tmp/par-combine-1\"\n"
      "interface Combine { combine : T -> T -> T }\n"
      "impl Combine for Bool {\n"
      "  combine(a) = {\n"
      "    @file:write_file(filename, \"combine\");\n"
      "    |b| a && b\n"
      "  }\n"
      "}\n"
      "main() = let f = combine(true), result = @file:read_file(filename) in\n"
      "  { @file:delete(filename); (result, f(false)) }"
    ))
  % We can only call combine() after we receive the second argument, which
  % determines the implementation, so the file isn't created.
  , ?_test({error, enoent} = Run(
      "filename = \"/tmp/par-combine-2\"\n"
      "interface Combine { combine : Int -> T -> T -> T }\n"
      "impl Combine for Bool {\n"
      "  combine(_) = {\n"
      "    @file:write_file(filename, \"combine\");\n"
      "    |a, b| a && b\n"
      "  }\n"
      "}\n"
      "main() = let _ = combine(1), result = @file:read_file(filename) in\n"
      "  { @file:delete(filename); result }"
    ))
  , ?_test({1, 3} = Run(
      "interface ToInt { to_int : T -> Int }\n"
      "impl ToInt for (Int, Bool) { to_int((a, _)) = a }\n"
      "impl ToInt for (Int, Bool, Int) { to_int((a, _, c)) = a + c }\n"
      "main() = (to_int((1, true)), to_int((1, false, 2)))"
    ))
  , ?_test(10 = Run(
      "interface ToInt { to_int : T -> Int }\n"
      "impl ToInt for Atom {\n"
      "  to_int(a) = @erlang:atom_to_list(a) |> @erlang:length/1\n"
      "}\n"
      "impl ToInt for [A ~ ToInt] {\n"
      "  to_int(l) = match l {\n"
      "    [h | t] => to_int(h) + to_int(t)\n"
      "    [] => 0\n"
      "  }\n"
      "}\n"
      "main() = to_int([@hello, @hey, @hi])"
    ))
  , ?_test(10 = Run(
      "interface ToInt { to_int : T -> Int }\n"
      "impl ToInt for Atom {\n"
      "  to_int(a) = @erlang:atom_to_list(a) |> @erlang:length/1\n"
      "}\n"
      "impl ToInt for [A ~ ToInt] {\n"
      "  to_int(l) = match l {\n"
      "    [h | t] => to_int(h) + to_int(t)\n"
      "    [] => 0\n"
      "  }\n"
      "}\n"
      "main() = (to_int : [A ~ ToInt] -> Int)([@hello, @hey, @hi])"
    ))
  , ?_test({<<"hi">>, <<"(no, yes)">>, <<"Foo(no)">>, <<"Foo((hey, yes))">>} = Run(
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
      "main() = (\n"
      "  to_str(\"hi\"),\n"
      "  to_str((false, true)),\n"
      "  to_str(Foo(false)),\n"
      "  to_str(Foo((\"hey\", true)))\n"
      ")"
    ))
  , ?_test([false, false, true] = Run(
      "interface Mappable { map : (A -> B) -> T<A> -> T<B> }\n"
      "list_map : (A -> B) -> [A] -> [B]\n"
      "list_map = @lists:map/2\n"
      "impl Mappable for List { map = list_map }\n"
      "main() = map(|x| x == 3, [1, 2, 3])"
    ))
  % to ensure code gen works even with iv unification
  , ?_test({true, $b} = Run(
      "interface Foo { foo : T -> T }\n"
      "interface Bar { bar : T -> T }\n"
      "impl Foo for Atom { foo(a) = a }\n"
      "impl Foo for (A ~ Foo, B) { foo((a, b)) = (foo(a), b) }\n"
      "baz(a, b) = let x = foo(a), y = foo(b), same = x == y in\n"
      "  (same, match x { (@hi, _) => 'a', _ => 'b' })\n"
      "main() = baz((@hey, 4), (@hey, 4))"
    ))
  % this time with multiple different ifaces
  , ?_test({false, $a} = Run(
      "interface Foo { foo : T -> T }\n"
      "interface Bar { bar : T -> T }\n"
      "impl Foo for Atom { foo(a) = a }\n"
      "impl Foo for (A ~ Foo, B) { foo((a, b)) = (foo(a), b) }\n"
      "impl Bar for Atom { bar(a) = a }\n"
      "impl Bar for (A ~ Bar, B) { bar((a, b)) = (bar(a), b) }\n"
      "baz(a, b) = let x = foo(a), y = bar(b), same = x == y in\n"
      "  (same, match x { (@hi, _) => 'a', _ => 'b' })\n"
      "main() = baz((@hi, 3), (@hey, 4))"
    ))

  %% , ?_test(3 = Run(
  %%     "interface ToInt { to_int : T -> Int }\n"
  %%     "impl ToInt for Int {\n"
  %%     "  to_int(i) = i\n"
  %%     "}\n"
  %%     "main() = to_int(3)"
  %%   ))
  %% , ?_test(2 = Run(
  %%     "interface ToInt { to_int : T -> Int }\n"
  %%     "impl ToInt for Float {\n"
  %%     "  to_int(f) = @erlang:round(f)\n"
  %%     "}\n"
  %%     "main() = to_int(1.6)"
  %%   ))
  %% , ?_test(3 = Run(
  %%     "interface ToInt { to_int : T -> Int }\n"
  %%     "impl ToInt for String {\n"
  %%     "  to_int = @erlang:byte_size/1\n"
  %%     "}\n"
  %%     "main() = to_int(\"hey\")"
  %%   ))
  %% , ?_test(8 = Run(
  %%     "interface ToInt { to_int : T -> Int }\n"
  %%     "impl ToInt for Ref {\n"
  %%     "  to_int(_) = 8\n"
  %%     "}\n"
  %%     "main() = to_int(@erlang:make_ref())"
  %%   ))
  %% , ?_test(6 = Run(
  %%     "interface ToInt { to_int : T -> Int }\n"
  %%     "impl ToInt for [Int] {\n"
  %%     "  to_int = @lists:foldl/3(|memo, num| memo + num, 0)\n"
  %%     "}\n"
  %%     "main() = to_int([1, 2, 3])"
  %%   ))
  %% , ?_test(936 = Run(
  %%     "interface ToInt { to_int : T -> Int }\n"
  %%     "impl ToInt for Map<Int, V> {\n"
  %%     "  to_int(m) = @erlang:hd(@maps:keys(m))\n"
  %%     "}\n"
  %%     "main() = to_int({ 936 => @value })"
  %%   ))
  %% , ?_test(-17 = Run(
  %%     "interface ToInt { to_int : T -> Int }\n"
  %%     "impl ToInt for () -> Int {\n"
  %%     "  to_int(f) = f()\n"
  %%     "}\n"
  %%     "main() = to_int(|-| -17)"
  %%   ))
  %% , ?_test(0 = Run(
  %%     "interface ToInt { to_int : T -> Int }\n"
  %%     "impl ToInt for () {\n"
  %%     "  to_int(_) = 0\n"
  %%     "}\n"
  %%     "main() = to_int(())"
  %%   ))
  %% , ?_test(28 = Run(
  %%     "interface ToInt { to_int : T -> Int }\n"
  %%     "impl ToInt for { a: Int, b: Int } {\n"
  %%     "  to_int(r) = r.a + r.b\n"
  %%     "}\n"
  %%     "main() = to_int({ a = 7, b = 21 })"
  %%   ))
  %% , ?_test(-3 = Run(
  %%     "interface ToInt { to_int : T -> Int }\n"
  %%     "impl ToInt for { A | target: Int } {\n"
  %%     "  to_int(r) = r.target\n"
  %%     "}\n"
  %%     "main() = to_int({ foo = \"hi\", bar = true, target = -3 })"
  %%   ))
  %% , ?_test(2 = Run(
  %%     "interface ToInt { to_int : T -> Int }\n"
  %%     "impl ToInt for Set<A> {\n"
  %%     "  to_int(s) = @gb_sets:size(@erlang:element(2, s))\n"
  %%     "}\n"
  %%     "main() = to_int(#['a', 'b'])"
  %%   ))
  %% , ?_test(30 = Run(
  %%     "interface ToInt { to_int : T -> Int }\n"
  %%     "enum Foo<A> { Bar(A) }\n"
  %%     "impl ToInt for Foo<Int> {\n"
  %%     "  to_int(Bar(i)) = i\n"
  %%     "}\n"
  %%     "main() = to_int(Bar(30))"
  %%   ))
  %% , ?_test(12 = Run(
  %%     "interface ToInt { to_int : T -> Int }\n"
  %%     "struct Foo { a : Int, b : Int }\n"
  %%     "impl ToInt for Foo {\n"
  %%     "  to_int(r) = r.a * r.b\n"
  %%     "}\n"
  %%     "main() = to_int(Foo { a = 3, b = 4 })"
  %%   ))
  ].

code_gen_pattern_test_() ->
  test_pattern(fun expr_code_gen/1, fun run_code_gen/1).
interpreter_pattern_test_() ->
  test_pattern(fun expr_interpreter/1, fun run_interpreter/1).
test_pattern(Expr, Run) ->
  [ ?_test(true = Expr("match 3 { 3 => true, 4 => false }"))
  , ?_test(18 = Expr("let x = 3 in match x + 5 { a => a + 10 }"))
  , ?_test(hello = Expr("match 'x' { 'y' => @hi, 'x' => @hello }"))
  , ?_test(5.0 = Expr("match |x| x { id => let y = id(true) in id(5.0) }"))
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
      "let x = [([], \"hi\", 3.0), ([2, 3], \"hey\", 58.0)] in"
      "  match x {\n"
      "    [([h | t], _, _) | _] => h\n"
      "    [_, ([], _, c)] => c\n"
      "    [(_, _, c), ([x, y | []], _, _)] => c + x - y\n"
      "  }"
    ))
  , ?_test([1, 2] = Expr(
      "let x = 3, y = [2] in match [1] { &y => y ++ [1], x => x ++ [2] }"
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
  , ?_test(hey = Run(
      "enum Foo<A> { Bar(Atom), Baz(A) }\n"
      "f(Bar(x), [Baz(y), Baz(x) | _]) = y\n"
      "main() = f(Bar(@hi), [Baz(@hey), Baz(@hi), Baz(@hello)])"
    ))
  , ?_assertError(function_clause, Run(
      "enum Foo<A> { Bar(Atom), Baz(A) }\n"
      "f(Bar(x), [Baz(y), Baz(x) | _]) = y\n"
      "main() = f(Bar(@hi), [Baz(@hey), Baz(@hello), Baz(@hello)])"
    ))


  , ?_test([] = Expr("let 3 = 3 in []"))
  , ?_test({5, 5.0} = Expr(
      "let [_, (x, _, _)] = [(1, \"foo\", @foo), (2, \"bar\", @bar)] in\n"
      "  (x + 3 : Int, x + 3.0)"
    ))
  , ?_test(7 = Expr("let [_, a] = [1, 3], (&a, b, &a) = (3, 7, 3) in b"))


  , ?_test({} = Expr("if let a = 3.0 then a"))
  % to ensure env is reset appropriately
  , ?_test(true = Expr("let a = true in { if let a = 3.0 then a; a }"))
  , ?_test(true = Expr("let a = true in { if let a = 3.0 then a else 5; a }"))
  , ?_test(<<"hey">> = Expr("if let (2, a) = (1, \"hi\") then a else \"hey\""))
  , ?_test(2.5 = Expr(
      "if let f = |b| if b then f(!b) + 1 else 1.5\n"
      "then f(true)\n"
      "else 0"
    ))
  ].

code_gen_import_test_() -> test_import(fun many_code_gen/2).
% TODO: defer interpreter import until we work on REPL
test_import(Many) ->
  [ ?_test(7 = Many([
      {"foo", "module Foo export x = 3"},
      {"bar", "module Bar import \"./foo\" main() = Foo.x + 4"}
    ], "bar"))
  , ?_test(7 = Many([
      {"foo", "module Foo export x = 3"},
      {"bar", "module Bar import \"./foo.par\" main() = Foo.x + 4"}
    ], "bar"))
  , ?_test(<<"hi">> = Many([
      {"foo", "module Foo x = 3"},
      {"bar", "module Bar import \"./foo\" main() = \"hi\""}
    ], "bar"))
  , ?_test(true = Many([
      {"foo", "module Foo export x = 3.0"},
      {"a/bar", "module Bar import \"../foo\" export x = Foo.x == 3.0"},
      {"b/baz", "module Baz import \"../a/bar\" main() = Bar.x || false"}
    ], "b/baz"))
  , ?_test([a, b, b] = Many([
      {"foo", "module Foo export x = [@a] export twice(x) = [x, x]"},
      {"a/bar",
        "module Bar\n"
        "import \"../foo\"\n"
        "import \"../b/baz\"\n"
        "main() = Foo.x ++ Baz.z"
      },
      {"b/baz",
        "module Baz\n"
        "import \"../foo\"\n"
        "export z = Foo.twice(@b)"
      }
    ], "a/bar"))
  , ?_test(100 = Many([
      {"foo",
        "module Foo\n"
        "import \"./bar\"\n"
        "export f(x) = Bar.g(x - 10.0)\n"
        "main() = f(27)"
      },
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "export g(x) = if x >= 0 then 10 * Foo.f(x) else 1"
      }
    ], "foo"))
  , ?_test({'BazInt', 3} = Many([
      {"foo", "module Foo enum Baz { BazInt(Int) }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "x : Foo.Baz\n"
        "x = Foo.BazInt(3)\n"
        "main() = x"
      }
    ], "bar"))
  , ?_assertEqual(
      #{a => 3},
      Many([
        {"foo", "module Foo struct Baz { a : Int }"},
        {"bar",
          "module Bar\n"
          "import \"./foo\"\n"
          "x : Foo.Baz\n"
          "x = Foo.Baz(3)\n"
          "main() = x"
        }
      ], "bar")
    )
  , ?_assertEqual(
      #{a => 3},
      Many([
        {"foo", "module Foo struct Baz { a : Int }"},
        {"bar",
          "module Bar\n"
          "import \"./foo\"\n"
          "main() = Foo.Baz { a = 3 }"
        }
      ], "bar")
    )
  , ?_assertEqual(
      #{a => 5},
      Many([
        {"foo", "module Foo struct Baz { a : Int }"},
        {"bar",
          "module Bar\n"
          "import \"./foo\"\n"
          "f(x) = Foo.Baz { x | a = 5 }\n"
          "main() = f(Foo.Baz { a = 3 })"
        }
      ], "bar")
    )
  , ?_test({'Foo', 3} = Many([
      {"foo", "module Foo enum Foo { Foo(Int) }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "x : Foo.Foo\n"
        "x = Foo.Foo(3)\n"
        "main() = x"
      }
    ], "bar"))
  , ?_test(7 = Many([
      {"foo", "module Foo enum Foo { Foo(Int) }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "x = match Foo.Foo(7) { Foo.Foo(n) => n }\n"
        "main() = x"
      }
    ], "bar"))
  , ?_assertEqual(
      {'Baz', #{a => 3}},
      Many([
        {"foo", "module Foo struct Baz { a : Int }"},
        {"bar",
          "module Bar\n"
          "import \"./foo\"\n"
          "enum Baz { Baz(Foo.Baz) }\n"
          "x : Baz\n"
          "x = Baz(Foo.Baz(3))\n"
          "main() = x"
        }
      ], "bar")
    )
  , ?_test(4 = Many([
      {"foo",
        "module Foo\n"
        "import \"./bar\"\n"
        "export a = Bar.b\n"
        "export c(x) = x + 1\n"
        "main() = a"
      },
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "export b = Foo.c(3)"
      }
    ], "foo"))


  , ?_test(7 = Many([
      {"foo", "module Foo export x = 3"},
      {"bar", "module Bar import \"./foo\" (x) main() = x + 4"}
    ], "bar"))
  , ?_test([a, b, b] = Many([
      {"foo", "module Foo export x = [@a] export twice(x) = [x, x]"},
      {"a/bar",
        "module Bar\n"
        "import \"../foo\" (x, twice)\n"
        "main() = x ++ twice(@b)"
      }
    ], "a/bar"))
  , ?_assertEqual(#{a => 3}, Many([
      {"foo", "module Foo struct Baz { a : Int }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\" (Baz)\n"
        "main() = Baz(3)"
      }
    ], "bar"))
  , ?_assertEqual({#{a => 3}, #{a => 4}}, Many([
      {"foo", "module Foo struct Baz { a : Int }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\" (Baz)\n"
        "x = Baz { a = 3 }\n"
        "y = Baz { { a = 3 } | a = 4 }\n"
        "main() = (x, y)"
      }
    ], "bar"))
  , ?_test({'Foo', 3} = Many([
      {"foo", "module Foo enum Baz { Foo(Int) }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\" (Baz)\n"
        "x : Baz\n"
        "x = Foo.Foo(3)\n"
        "main() = x"
      }
    ], "bar"))
  , ?_test({'Foo', 3} = Many([
      {"foo", "module Foo enum Foo { Foo(Int) }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\" (Foo)\n"
        "x : Foo\n"
        "x = Foo(3)\n"
        "main() = x"
      }
    ], "bar"))
  , ?_test(2 = Many([
      {"foo", "module Foo enum Foo { One, Two, Three }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\" (One, Two, Three)\n"
        "f(x) = match x { One => 1, Two => 2, Three => 3 }\n"
        "main() = f(Two)"
      }
    ], "bar"))
  , ?_test(3 = Many([
      {"foo", "module Foo enum Foo { One, Two, Three }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\" (variants Foo)\n"
        "f(x) = match x { One => 1, Two => 2, Three => 3 }\n"
        "main() = f(Three)"
      }
    ], "bar"))
  , ?_assertEqual(#{start_line => 18}, Many([
      {"foo", "module Foo struct Loc { start_line : Int }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\" (Loc)\n"
        "f : Loc -> Loc\n"
        "f(l) = { start_line = l.start_line + 1 }\n"
        "main() = f({ start_line = 17 })"
      }
    ], "bar"))


  , ?_assertEqual($a + $b, Many([
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
        "main() = Foo.to_int(('a', 'b'))"
      }
    ], "bar"))
  , ?_assertEqual($a + $b, Many([
      {"foo", "module Foo interface ToInt { to_int : T -> Int }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "impl Foo.ToInt for Char { to_int(c) = $c }\n"
        "impl Foo.ToInt for (A ~ Foo.ToInt, B ~ Foo.ToInt) {\n"
        "  to_int((a, b)) = Foo.to_int(a) + Foo.to_int(b)\n"
        "}\n"
        "main() = Foo.to_int(('a', 'b'))"
      }
    ], "bar"))
  , ?_assertEqual($a + $b, Many([
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
        "main() = Foo.to_int(('a', 'b'))"
      }
    ], "bar"))
  , ?_assertEqual($a + $b, Many([
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
        "main() = Foo.to_int(('a', 'b'))"
      }
    ], "bar"))
  , ?_assertEqual($a + $b, Many([
      {"foo", "module Foo interface ToInt { to_int : T -> Int }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\" (ToInt)\n"
        "impl ToInt for Char { to_int(c) = $c }\n"
        "impl ToInt for (A ~ ToInt, B ~ ToInt) {\n"
        "  to_int((a, b)) = Foo.to_int(a) + Foo.to_int(b)\n"
        "}\n"
        "main() = Foo.to_int(('a', 'b'))"
      }
    ], "bar"))
  , ?_assertEqual($a + $b, Many([
      {"foo", "module Foo interface ToInt { to_int : T -> Int }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\" (ToInt, to_int)\n"
        "impl ToInt for Char { to_int(c) = $c }\n"
        "impl ToInt for (A ~ ToInt, B ~ ToInt) {\n"
        "  to_int((a, b)) = to_int(a) + to_int(b)\n"
        "}\n"
        "main() = to_int(('a', 'b'))"
      }
    ], "bar"))
  ].
