-module(exec_test).
-export([returns_fun/0]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/common.hrl").

run_code_gen(Prg) ->
  Result = type_system_test:infer_prefix(Prg),
  {ok, Comps, C, _} = type_system_test:check_ok(Result),
  % Anything that calls run_code_gen() is expected to not be reliant on the
  % standard library or any other modules.
  {Compiled, _} = code_gen:compile_comps(Comps, C),
  [{compiled, Mod, Binary} | _] = Compiled,

  utils:remove_mod(Mod),
  code:load_binary(Mod, "", Binary),

  par_native:init(Mod),
  Mod:main().

run_interpreter(Prg) ->
  Result = type_system_test:infer_prefix(Prg),
  {ok, [#comp{ast=Ast}], _, _} = type_system_test:check_ok(Result),
  interpreter:run_ast(Ast, []).

expr_code_gen(Expr) -> run_code_gen("main() =\n" ++ Expr).
expr_interpreter(Expr) -> run_interpreter("main() =\n" ++ Expr).

many_code_gen(PathPrgs, TargetPath) ->
  Dir = utils:temp_dir(),
  Result = type_system_test:infer_many(
    Dir,
    PathPrgs,
    TargetPath
  ),
  {ok, Comps, C, _} = type_system_test:check_ok(Result),

  {Compiled, _} = code_gen:compile_comps(Comps, C),
  MainMod = utils:prep_compiled(Compiled, Dir),

  V = MainMod:main(),
  utils:remove_compiled(Compiled, Dir),
  V.

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
  , ?_test(h = Expr("@h"))
  , ?_test(hello = Expr("@hello"))
  , ?_test('empty?' = Expr("@empty?"))
  , ?_test('hello world' = Expr("@\"hello world\""))
  , ?_test([3.0, 5] = Expr("[3.0, 5]"))
  , ?_test({<<"what">>, false, 7} = Expr("(\"what\", false, 7)"))
  , ?_assertEqual(#{}, Expr("{}"))
  , ?_assertEqual(
      #{<<"hello">> => <<"world">>, <<"some">> => <<"thing">>},
      Expr("{\"hello\" => \"world\", \"some\" => \"thing\"}")
    )
  , ?_assertEqual(#{'_@type' => 'Set'}, Expr("#[]"))
  , ?_assertEqual(
      #{'_@type' => 'Set', 2 => true, 4 => true, 6 => true, 8 => true},
      Expr("#[2, 4, 2, 6, 4, 8, 6]")
    )


  , ?_test({3.0, true} = (Expr("|x| x"))({3.0, true}))
  , ?_test(35.0 = (Expr("|x, y| x * y * 3.5"))(4, 2.5))
  , ?_test(true = Expr("(|x| x || true)(false)"))
  , ?_test(<<"ab">> = Expr("(|a, b| a ++ b)(\"a\", _)(\"b\")"))
  , ?_test(5 = Expr("(|x| |y| x + y)(2)(3)"))
  , ?_test([4, 3, 1, 3] = Expr("(|x| |-| x ++ [3])([4, 3, 1])()"))
  % to test code_gen_utils:'_@curry' in the parital application case
  , ?_test(4 = Expr(
      "let f = (|a| |b, c, d| a - b + c - d)(4)\n"
      "let f = f(_, 3, _)\n"
      "f(2, 1)"
    ))


  , ?_test(<<"world">> = Expr("if false then \"hello\" else \"world\""))
  , ?_test([true, false] =
             Expr("if false || true && 3.5 < 4 then [true, false] else [true]"))
  , ?_test({} = Expr("if true then @foo"))
  , ?_test({} = Expr("if false then @io:nl() : () else discard 3"))
  % ensures that we handle conditions that aren't valid guard clauses
  , ?_test($a = Expr(
      "let f = |x| x == 3\n"
      "if f(3) then 'a' else 'b'"
    ))

  , ?_test(5 = Expr(
      "let x = 5\n"
      "x"
    ))
  % ensures that we generate a unique name for each variable; otherwise, we'll
  % get a badmatch 4 <=> 5
  , ?_test(5 = Expr(
      "let x =\n"
      "  let x = 4\n"
      "  let y = 5\n"
      "  y\n"
      "x"
    ))
  , ?_test(true = Expr(
      "let x = 5\n"
      "let y = true\n"
      "x == 4 || y"
    ))
  , ?_test(false = Expr(
      "let and = |a, b, c| a && b && c\n"
      "and(true, true, false)"
    ))
  , ?_test([4, 3, 4, 2, 3] = Expr(
      "let a = [4]\n"
      "let f(x) = a ++ x ++ [3]\n"
      "f([]) ++ f([2])"
    ))
  , ?_test(15 = Expr(
      "let a = 10\n"
      "let b = a + 5\n"
      "b"
    ))
  , ?_test(32 = Expr(
      "let f = |x, c| if x == 0 then c else f(x - 1, c * 2)\n"
      "f(5, 1)"
    ))
  , ?_test(true = Expr(
      "let a = 1\n"
      "let a = a == 1\n"
      "a"
    ))


  , ?_test(true = Expr(
      "@foo\n"
      "true"
    ))
  , ?_assertEqual(#{<<"hi">> => 5}, Expr(
      "let x = 5\n"
      "@erlang:hd([1])\n"
      "3.0\n"
      "{ \"hi\" => x }"
    ))

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
  , ?_test(false = Expr("\"hi\" < \"hello\""))
  , ?_test(true = Expr("'n' > 'm'"))
  , ?_test(true = Expr("\"some\" >= \"some\""))
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
      #{'_@type' => 'Set', 1 => true, 2 => true, 3 => true},
      Expr("#[1] ++ #[2, 3]")
    )
  , ?_test(-3 = Expr("-3"))
  , ?_test(-78.5 = Expr("-5 * 15.7"))
  , ?_test(false = Expr("!true"))
  , ?_test(true = Expr("!false && true"))
  , ?_test($h = Expr("$'h'"))
  , ?_test(foo = Expr("assume @foo"))


  , ?_test([4, 6] = Expr("@lists:filter(|x| x > 3, [2, 4, 6])"))
  , ?_test([6] = Expr("@lists:filter((|t, x| x > t)(5, _), [2, 4, 6])"))
  , ?_test([true] = Expr("@lists:map(@erlang:is_atom/1, [@a])"))
  , ?_test(3 = Expr("@exec_test:returns_fun()(1, 2)"))
  , ?_test(true = Expr(
      "let foo(x) = x == ()\n"
      "foo(())"
    ))

  , ?_test(<<"hello world">> = Expr("\"hello\" |> |x| x ++ \" world\""))
  , ?_test(77 = Expr(
      "let inc(x) = x + 1\n"
      "(5 |> |x| 2 * x |> inc) * 7"
    ))
  , ?_test({<<"hihey">>, false} = (Expr(
      "let f(x, y) = (x ++ \"hey\", y && true)\n"
      "\"hi\" |> f(_)"
    ))(false))
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
      "main() = cmp(and_true, _, _)(two, false)"
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
  , ?_test(true = Run(
      "empty? = true\n"
      "main() =\n"
      "  let maybe? = true\n"
      "  maybe? || empty?"
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
      "foo = bar(baz(\"hi\", _), _, _)\n"
      "main() = foo(3, 4)"
    ))
  % to ensure globals are evaluated strictly in order
  , ?_test("hi" = Run(
      "foo = to_list(\"hi\")\n"
      "to_list = @erlang:binary_to_list/1\n"
      "main() = foo"
    ))
  % to ensure globals are only evaluated once
  , ?_test(baz = Run(
      "foo = @erlang:put(@globals_once, @baz)\n"
      "bar = @erlang:erase(@globals_once)\n"
      "main() = bar"
    ))
  % to ensure partial app function and args are only evaluated once
  , ?_test(5 = Run(
      "key = @partial_app_count\n"
      "inc() = @erlang:put(key, @erlang:get(key) + 1)\n"
      "foo() =\n"
      "  inc()\n"
      "  |_, _| inc()\n"
      "main() =\n"
      "  @erlang:put(key, 0)\n"
      "  let f = foo()(inc(), _)\n"
      "  f(1)\n"
      "  f(@hi)\n"
      "  f(true)\n"
      "  @erlang:get(key)"
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
      "main() = Bar(_, [\"hello\"])"
    ))(true))
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

code_gen_exception_test_() ->
  test_exception(fun expr_code_gen/1, fun run_code_gen/1, fun many_code_gen/2).
%% interpreter_exception_test_() ->
%%   test_exception(fun expr_interpreter/1, fun run_interpreter/1).
test_exception(Expr, Run, Many) ->
  [ ?_test('Mod.Bar' = Run(
      "exception Bar\n"
      "main() = Bar"
    ))
  , ?_test({'Mod.Baz', 5} = Run(
      "exception Baz(Int)\n"
      "main() = Baz(5)"
    ))
  , ?_test({'Mod.Bar', true, [<<"hi">>, <<"hey">>]} = (Run(
      "exception Bar(Bool, [String])\n"
      "main() = Bar(true, _)"
    ))([<<"hi">>, <<"hey">>]))


  , ?_assertThrow('Mod.Bar', Run(
      "exception Bar\n"
      "main() = raise Bar"
    ))
  , ?_assertThrow({'Mod.Bar', 3}, Run(
      "exception Bar(Int)\n"
      "bar = Bar(3)\n"
      "main() = raise bar"
    ))
  , ?_test(1 = Expr("try 1 catch { _ => 2 }"))
  , ?_test(hey = Run(
      "exception Bar\n"
      "main() = try raise Bar catch { Bar => @hey }\n"
    ))
  , ?_assertThrow('Mod.Bar', Run(
      "exception Bar\n"
      "exception Baz\n"
      "main() = try raise Bar catch { Baz => 'a' }\n"
    ))
  , ?_test(4.2 = Run(
      "exception Bar([Float], Float)\n"
      "bar(b) = if b then raise Bar([1.7], 2.5) else 5.8\n"
      "baz(x, b) = x + bar(b)\n"
      "main() = try baz(7, true) catch { Bar([a], b) => a + b }"
    ))
  , ?_test(<<"hello">> = Expr("ensure @world after \"hello\""))
  , ?_test(begin
      ?assertThrow('Mod.Bar', Run(
        "exception Bar\n"
        "main() =\n"
        "  @erlang:put(@ensure, @baz)\n"
        "  ensure @erlang:erase(@ensure) after raise Bar"
      )),
      undefined = get(ensure)
    end)
  , ?_test(bar = Many([
      {"foo",
        "module Foo\n"
        "exception Baz"
      },
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "exception Baz\n"
        "main() = try raise Baz catch { Foo.Baz => @foo, Baz => @bar }\n"
      }
    ], "bar"))
  ].

code_gen_record_test_() ->
  test_record(fun expr_code_gen/1, fun run_code_gen/1).
%% interpreter_record_test_() ->
%%   test_record(fun expr_interpreter/1, fun run_interpreter/1).
test_record(Expr, Run) ->
  [ ?_assertEqual(#{'_@type' => '_@Record', bar => 3}, Expr("{ bar = 3 }"))
  , ?_assertEqual(
      #{'_@type' => '_@Record', bar => 3, baz => true},
      Expr("{ bar = 3, baz = true }")
    )
  , ?_test(8 = Expr("{ bar = |x| x + 5 }.bar(3)"))
  , ?_test(5 = Expr("{ abs(x) = if x > 0 then x else abs(-x) }.abs(-5)"))
  , ?_assertEqual(
      #{'_@type' => '_@Record', bar => 4.0},
      Expr("{ bar = 4.0 | { bar = 3 } }")
    )
  , ?_assertEqual(
      #{'_@type' => '_@Record', bar => true},
      Expr("{ bar := true | { bar = 3 } }")
    )
  , ?_assertEqual(
      #{'_@type' => '_@Record', bar => true, baz => hey},
      Expr("{ bar := true, baz = @hey | { bar = 3, baz = @hi } }")
    )
  , ?_assertEqual(
      #{'_@type' => '_@Record', bar => true, baz => 3.0},
      Expr("{ bar := true, baz := 3.0 | { bar = 3, baz = @hi } }")
    )

  , ?_test(false = Expr("{ bar = 3 } == { bar = 5 }"))
  , ?_test(true = Expr("{ bar = 3 } == { bar = 3 }"))


  , ?_test(true = Expr(
      "let f(x) = x.bar || false\n"
      "f({ bar = true })"
    ))
  , ?_test(hi = Expr(
      "let f(x) = x.bar\n"
      "f({ bar = @hi, baz = 7 })"
    ))

  , ?_test({11, <<"oh, hi">>} = Run(
      "f(x) = (x.bar + 4, x.foo ++ \"hi\")\n"
      "main() = f({ bar = 7, foo = \"oh, \" })"
    ))

  % named struct
  , ?_assertEqual(#{'_@type' => 'Foo', bar => 3}, Run(
      "struct Foo { bar : Int }\n"
      "main() = Foo(3)"
    ))
  , ?_assertEqual(#{'_@type' => 'Foo', bar => 3}, Run(
      "struct Foo { bar : Int }\n"
      "main() = Foo { bar = 3 }"
    ))
  , ?_assertEqual(#{'_@type' => 'Foo', bar => 3, baz => [<<"hello">>]}, (Run(
      "struct Foo { bar : Int, baz : [String] }\n"
      "main() = Foo(3, _)"
    ))([<<"hello">>]))
  , ?_assertEqual(#{'_@type' => 'Foo', baz => [first, second], bar => 15}, Run(
      "struct Foo { bar : Int, baz : [Atom] }\n"
      "main() = Foo { baz = [@first, @second], bar = 15 }"
    ))
  , ?_assertEqual(#{'_@type' => 'Foo', bar => true, baz => hi}, (Run(
      "struct Foo<X, Y> { bar : X, baz : Y }\n"
      "main() = Foo(_, @hi)"
    ))(true))
  , ?_assertEqual(#{'_@type' => 'Foo', bar => hi}, Run(
      "struct Foo<X> { bar : X }\n"
      "main() = Foo { bar = @hi }"
    ))
  % Won't be able to create a valid Foo, but should still type check.
  , ?_test(true = Run(
      "struct Foo { baz : Foo }\n"
      "main() = true"
    ))
  , ?_assertEqual(
      #{'_@type' => 'Foo', bar => hi, baz => [
        #{'_@type' => 'Foo', bar => hello, baz => []}
      ]},
      Run(
        "struct Foo { bar : Atom, baz : [Foo] }\n"
        "main() = Foo { bar = @hi, baz = [Foo { bar = @hello, baz = [] }] }"
      )
    )


  % named struct updates
  , ?_assertEqual(#{'_@type' => 'Foo', bar => 7}, Run(
      "struct Foo { bar : Int }\n"
      "f(x) = { bar = 7 | x : Foo }\n"
      "main() = f({ bar = 3 })"
    ))
  , ?_assertEqual(#{'_@type' => '_@Record', bar => true}, Run(
      "struct Foo { bar : Int }\n"
      "foo = Foo { bar = 3 }\n"
      "main() = { bar := true | foo }"
    ))
  , ?_assertEqual(#{'_@type' => '_@Record', bar => true, baz => [<<"hi">>]}, Run(
      "struct Foo<A> { bar : A, baz : [String] }\n"
      "foo = Foo { bar = @a, baz = [\"hi\"] }\n"
      "main() = { bar := true | foo }"
    ))
  , ?_assertEqual(#{'_@type' => 'Foo', bar => true, baz => [<<"hi">>]}, Run(
      "struct Foo<A> { bar : A, baz : [String] }\n"
      "foo = Foo { bar = @a, baz = [\"hi\"] }\n"
      "main() = Foo { bar := true | foo }"
    ))


  % generalization cases
  , ?_test({<<"hi">>, true} = Run(
      "struct Foo<A> { bar : A }\n"
      "main() =\n"
      "  let id(a) = a\n"
      "  let f = Foo { bar = id }\n"
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
  IfaceToI = "interface ToI { to_i : T -> Int }\n",
  BoolImpl = "impl ToI for Bool {\n"
    "  to_i(b) = if b then 1 else 0\n"
    "}\n",
  IfaceImpl = IfaceToI ++ BoolImpl ++ "\n",

  [ ?_test(1 = Run(IfaceImpl ++ "main() = to_i(true)"))
  , ?_test(3 = Run(
      IfaceToI ++
      "impl ToI for Int {\n"
      "  to_i(i) = i\n"
      "}\n"
      "main() = to_i(3 : Int)"
    ))
  , ?_test(2 = Run(
      IfaceToI ++
      "impl ToI for Float {\n"
      "  to_i(f) = @erlang:round(f)\n"
      "}\n"
      "main() = to_i(1.6)"
    ))
  , ?_test(3 = Run(
      IfaceToI ++
      "impl ToI for String {\n"
      "  to_i = @erlang:byte_size/1\n"
      "}\n"
      "main() = to_i(\"hey\")"
    ))
  , ?_test(8 = Run(
      IfaceToI ++
      "impl ToI for Ref {\n"
      "  to_i(_) = 8\n"
      "}\n"
      "main() = to_i(@erlang:make_ref() : Ref)"
    ))
  , ?_test(6 = Run(
      IfaceToI ++
      "impl ToI for [Int] {\n"
      "  to_i = @lists:foldl/3(|memo, num| memo + num, 0, _)\n"
      "}\n"
      "main() = to_i([1, 2, 3])"
    ))
  , ?_test(936 = Run(
      IfaceToI ++
      "impl ToI for Map<Int, V> {\n"
      "  to_i(m) = @erlang:hd(@maps:keys(m))\n"
      "}\n"
      "main() = to_i({ 936 => @value })"
    ))
  , ?_test(-17 = Run(
      IfaceToI ++
      "impl ToI for () -> Int {\n"
      "  to_i(f) = f()\n"
      "}\n"
      "main() = to_i(|-| -17)"
    ))
  , ?_test(0 = Run(
      IfaceToI ++
      "impl ToI for () {\n"
      "  to_i(_) = 0\n"
      "}\n"
      "main() = to_i(())"
    ))
  , ?_test(1 = Run(
      IfaceToI ++
      "impl ToI for (Int, Bool) { to_i((a, _)) = a }\n"
      "main() = to_i((1, true))"
    ))
  , ?_test(28 = Run(
      IfaceToI ++
      "impl ToI for { a: Int, b: Int } {\n"
      "  to_i(r) = r.a + r.b\n"
      "}\n"
      "main() = to_i({ a = 7, b = 21 })"
    ))
  , ?_test(-3 = Run(
      IfaceToI ++
      "impl ToI for { target: Int | A } {\n"
      "  to_i(r) = r.target\n"
      "}\n"
      "main() = to_i({ foo = \"hi\", bar = true, target = -3 })"
    ))
  % subtract 1 from map_size to account for tag
  , ?_test(2 = Run(
      IfaceToI ++
      "impl ToI for Set<A> {\n"
      "  to_i(s) = @erlang:map_size(s) - 1\n"
      "}\n"
      "main() = to_i(#['a', 'b'])"
    ))
  , ?_test(30 = Run(
      IfaceToI ++
      "enum Foo<A> { Bar(A) }\n"
      "impl ToI for Foo<Int> {\n"
      "  to_i(Bar(i)) = i\n"
      "}\n"
      "main() = to_i(Bar(30))"
    ))
  , ?_test(12 = Run(
      IfaceToI ++
      "struct Foo { a : Int, b : Int }\n"
      "impl ToI for Foo {\n"
      "  to_i(r) = r.a * r.b\n"
      "}\n"
      "main() = to_i(Foo { a = 3, b = 4 })"
    ))


  % rewriting cases
  , ?_test(0 = Run(IfaceImpl ++ "main() = (to_i : Bool -> Int)(false)"))
  , ?_test(1 = Run(IfaceImpl ++ "main() = (to_i : T ~ ToI -> Int)(true)"))
  , ?_test(0 = Run(
      IfaceImpl ++
      "foo([_, f]) = f(false)\n"
      "main() =\n"
      "  let list = [to_i, to_i]\n"
      "  foo(list)"
    ))
  , ?_test(1 = Run(
      IfaceImpl ++
      "foo((f, _)) = f(true)\n"
      "main() =\n"
      "  let tuple = (to_i, 1)\n"
      "  foo(tuple)"
    ))
  , ?_test(0 = Run(
      IfaceImpl ++
      "first : Set<A> -> A\n"
      "first(set) =\n"
      "  let elems = @maps:keys(@maps:remove(@\"_@type\", set))\n"
      "  @erlang:hd(elems)\n"
      "foo(set) = first(set)(false)\n"
      "main() =\n"
      "  let set = #[to_i]\n"
      "  foo(set)"
    ))
  , ?_test(1 = Run(
      IfaceImpl ++
      "key : Map<K, V> -> K\n"
      "key(map) = @erlang:hd(@maps:keys(map))\n"
      "foo(map) = key(map)(true)\n"
      "main() =\n"
      "  let map = { to_i => 1 }\n"
      "  foo(map)"
    ))
  , ?_test(0 = Run(
      IfaceImpl ++
      "value : Map<K, V> -> V\n"
      "value(map) = @erlang:hd(@maps:values(map))\n"
      "foo(map) = value(map)(false)\n"
      "main() =\n"
      "  let map = { 1 => to_i }\n"
      "  foo(map)"
    ))
  , ?_test(1 = Run(
      IfaceImpl ++
      "foo(record) = record.b(true)\n"
      "main() =\n"
      "  let record = { a = true, b = to_i }\n"
      "  foo(record)"
    ))
  , ?_test(0 = Run(
      IfaceImpl ++
      "foo(record) = record.b(false)\n"
      "bar(record) =\n"
      "  let new_record = { b := to_i | record }\n"
      "  foo(new_record)\n"
      "main() = bar({ a = true, b = 35.0 })"
    ))
  , ?_test(1 = Run(
      IfaceImpl ++
      "struct Foo<A> { a : (), b : A }\n"
      "bar(foo) = foo.b(true)\n"
      "main() =\n"
      "  let foo = Foo { a = (), b = to_i }\n"
      "  bar(foo)"
    ))
  , ?_test({0, -1} = Run(
      IfaceImpl ++
      "enum Foo<A> { Bar, Baz(Int), Call(Bool, A) }\n"
      "bar(foo) = match foo { Call(b, f) => f(b), _ => -1 }\n"
      "main() =\n"
      "  let foo = Call(false, to_i)\n"
      "  let baz = Baz(3)\n"
      "  foo == baz\n"
      "  (bar(foo), bar(baz))"
    ))
  , ?_test(2 = Run(
      IfaceImpl ++
      "struct Foo<A> { a : A, other_a : A }\n"
      "enum Bar<A, B> { Cat(A), Dog(B) }\n"
      "first : Set<A> -> A\n"
      "first(set) =\n"
      "  let elems = @maps:keys(@maps:remove(@\"_@type\", set))\n"
      "  @erlang:hd(elems)\n"
      "key : Map<K, V> -> K\n"
      "key(map) = @erlang:hd(@maps:keys(map))\n"
      "bar(foo) =\n"
      "  let Cat(s) = foo.a\n"
      "  let Dog([m]) = foo.other_a\n"
      "  first(s)(true) + key(m)(true)\n"
      "main() =\n"
      "  let foo = Foo {\n"
      "    a = Cat(#[to_i])\n"
      "    other_a = Dog([{to_i => 1}])\n"
      "  }\n"
      "  bar(foo)"
    ))
  , ?_test(0 = Run(
      IfaceImpl ++
      "impl ToI for [Int] { to_i([i]) = i }\n"
      "hd : T<A> -> A\n"
      "hd(_) = @erlang:hd([to_i : Bool -> Int])\n"
      "bar(l) = hd(l)(false)\n"
      "main() =\n"
      "  let foo = @io:printable_range() : T<A ~ ToI -> Int>\n"
      "  bar(foo)"
    ))


  , ?_test(0 = Run(
      IfaceImpl ++
      "proxy(b) = to_i(b)\n"
      "main() = proxy(false)"
    ))
  % to ensure no impl arg is added to lambda |c| ... because of bound impl b
  , ?_test(1 = Run(
      IfaceImpl ++
      "foo(b) = |c| if b == c then to_i(c) else -1\n"
      "main() = foo(true)(true)"
    ))
  % to test fns with multiple arguments having the same iv pair
  , ?_test(7 = Run(
      IfaceToI ++
      "impl ToI for Float {\n"
      "  to_i(n) = @erlang:round(n)\n"
      "}\n"
      "foo(a, b) = if a == b then to_i(a) * 2 else to_i(a) + to_i(b)\n"
      "main() = foo(3.7, 3.1)"
    ))
  % to test recursive fns that we can't inst
  , ?_test(2 = Run(
      IfaceImpl ++
      "foo(twice, b) = if twice then 2 * foo(false, b) else to_i(b)\n"
      "main() = foo(true, true)"
    ))
  % this time, a fn that's both recursive and with bound variables
  , ?_test(4 = Run(
      IfaceImpl ++
      "foo(t, b) =\n"
      "  let bar(twice, c) =\n"
      "    if twice then\n"
      "      2 * bar(false, c)\n"
      "    else if b == c then\n"
      "      2 * to_i(c)\n"
      "    else\n"
      "      to_i(c)\n"
      "  bar(t, b)\n"
      "main() = foo(true, true)"
    ))
  , ?_test({2, 3} = Run(
      IfaceToI ++
      "impl ToI for [A] { to_i(l) = @erlang:length(l) }\n"
      "interface Foo { foo : (T, (T, A ~ ToI)) -> Int }\n"
      "impl Foo for Bool {\n"
      "  foo(a, (b, c)) = if b && a then 2 * to_i(c) else to_i(c)\n"
      "}\n"
      "main() = (foo(true, (true, [1])), foo(false, (true, ['a', 'b', 'c'])))"
    ))
  , ?_test({1, 2} = Run(
      IfaceToI ++
      "impl ToI for [A] { to_i(l) = @erlang:length(l) }\n"
      "interface Foo { foo : (T, (T, A ~ ToI)) -> Int }\n"
      "impl Foo for Bool {\n"
      "  foo(a, (b, c)) = if b && a then 2 * to_i(c) else to_i(c)\n"
      "}\n"
      "main() = (\n"
      "  (foo : (T ~ Foo, (T ~ Foo, [Int])) -> Int)(true, (false, [1])),\n"
      "  (foo : (Bool, (Bool, A ~ ToI)) -> Int)(false, (false, [@a, @b]))\n"
      ")"
    ))
  , ?_test({foo, false} = Run(
      "interface Combine { combine : T -> T -> T }\n"
      "impl Combine for Bool {\n"
      "  combine(a) =\n"
      "    @erlang:put(@combine1, @foo)\n"
      "    |b| a && b\n"
      "}\n"
      "main() =\n"
      "  let f = combine(true)\n"
      "  let result = @erlang:erase(@combine1)\n"
      "  (result, f(false))"
    ))
  , ?_test(foo = Run(
      "interface Combine { combine : Int -> (T, T) -> T }\n"
      "impl Combine for Bool {\n"
      "  combine(_) =\n"
      "    @erlang:put(@combine2, @foo)\n"
      "    |a, b| a && b\n"
      "}\n"
      "main() =\n"
      "  combine(1) : (Bool, Bool) -> Bool\n"
      "  @erlang:erase(@combine2)\n"
    ))
  , ?_test({1, 3} = Run(
      IfaceToI ++
      "impl ToI for (Int, Bool) { to_i((a, _)) = a }\n"
      "impl ToI for (Int, Bool, Int) { to_i((a, _, c)) = a + c }\n"
      "main() = (to_i((1, true)), to_i((1, false, 2)))"
    ))
  , ?_test(10 = Run(
      IfaceToI ++
      "impl ToI for Atom {\n"
      "  to_i(a) = @erlang:atom_to_list(a) |> @erlang:length/1\n"
      "}\n"
      "impl ToI for [A ~ ToI] {\n"
      "  to_i(l) = match l {\n"
      "    [h | t] => to_i(h) + to_i(t)\n"
      "    [] => 0\n"
      "  }\n"
      "}\n"
      "main() = to_i([@hello, @hey, @hi])"
    ))
  , ?_test(10 = Run(
      IfaceToI ++
      "impl ToI for Atom {\n"
      "  to_i(a) = @erlang:atom_to_list(a) |> @erlang:length/1\n"
      "}\n"
      "impl ToI for [A ~ ToI] {\n"
      "  to_i(l) = match l {\n"
      "    [h | t] => to_i(h) + to_i(t)\n"
      "    [] => 0\n"
      "  }\n"
      "}\n"
      "main() = (to_i : [A ~ ToI] -> Int)([@hello, @hey, @hi])"
    ))
  , ?_assertEqual(
      {<<"hi">>, <<"(no, yes)">>, <<"Foo(no)">>, <<"Foo((hey, yes))">>},
      Run(
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
      )
    )
  , ?_test({93, true} = Run(
      "interface FromStr { from_str : String -> T }\n"
      "impl FromStr for Int { from_str = @erlang:binary_to_integer/1 }\n"
      "impl FromStr for Bool { from_str(s) = s == \"true\" }\n"
      "main() = (from_str(\"93\") : Int, from_str(\"true\") : Bool)\n"
    ))
  , ?_test({false, 3} = Run(
      "interface Const { const : () -> T }\n"
      "impl Const for Int { const() = 3 }\n"
      "impl Const for Bool { const() = false }\n"
      "main() = (const() : Bool, const() : Int)"
    ))
  , ?_test({3, false} = Run(
      "interface Const { const : () -> T }\n"
      "impl Const for Int { const() = 3 }\n"
      "impl Const for Bool { const() = false }\n"
      "impl Const for (A ~ Const, B ~ Const) { const() = (const(), const()) }\n"
      "main() = const() : (Int, Bool)"
    ))
  , ?_test({3, 3} = Run(
      "interface Const { const : () -> T }\n"
      "impl Const for Int { const() = 3 }\n"
      "impl Const for Bool { const() = false }\n"
      "impl Const for (A ~ Const, B ~ Const) { const() = (const(), const()) }\n"
      "foo = const : () -> (Int, B ~ Const)"
      "main() = foo() : (Int, Int)"
    ))
  , ?_test(3 = Run(
      "interface Const { const : () -> T }\n"
      "impl Const for Int { const() = 3 }\n"
      "foo = const\n"
      "main() = foo() : Int"
    ))
  , ?_test(3 = Run(
      "interface Const { const : () -> T }\n"
      "impl Const for Int { const() = 3 }\n"
      "foo([_]) = const\n"
      "main() = foo([@hi])() : Int"
    ))
  , ?_test([false, false, true] = Run(
      "interface Mappable { map : (A -> B, T<A>) -> T<B> }\n"
      "list_map : (A -> B, [A]) -> [B]\n"
      "list_map = @lists:map/2\n"
      "impl Mappable for List { map = list_map }\n"
      "main() = map(|x| x == 3, [1, 2, 3])"
    ))
  , ?_assertEqual(#{a => $a}, Run(
      "interface Mappable { map : (A -> B, T<A>) -> T<B> }\n"
      "map_map : (((A, B)) -> (C, D), Map<A, B>) -> Map<C, D>\n"
      "map_map(f, m) =\n"
      "  let cb = |k, v, new_m|\n"
      "    let (new_k, new_v) = f((k, v))\n"
      "    @maps:put(new_k, new_v, new_m)\n"
      "  @maps:fold(cb, {}, m)\n"
      "impl Mappable for Map { map = map_map }\n"
      "main() = map(|(k, v)| (v, k), { 'a' => @a })"
    ))
  , ?_test($a = Run(
      "interface Foo { foo : T<(Int, Bool)> -> Char }\n"
      "impl Foo for Map { foo(_) = 'a' }\n"
      "main() = foo({ 3 => true })"
    ))
  , ?_assertEqual(#{<<"key">> => value}, Run(
      "interface FromList { from_list : [A] -> T<A> }\n"
      "impl FromList for Map { from_list([(k, v)]) = { k => v } }\n"
      "main() = from_list([(\"key\", @value)]) : Map<String, Atom>"
    ))
  , ?_assertEqual(#{first => $f, second => $s}, Run(
      "interface ToMap { to_map : T<K, V> -> Map<K, V> }\n"
      "impl ToMap for List { to_map = @maps:from_list/1 }\n"
      "main() = to_map([(@first, 'f'), (@second, 's')])"
    ))
  , ?_test(true = Run(
      "interface Foo { foo : T -> T }\n"
      "impl Foo for Int { foo(i) = 2 * i }\n"
      "impl Foo for [A ~ Foo] {\n"
      "  foo(l) = match l { [] => l, [h | t] => [foo(h) | foo(t)] }\n"
      "}\n"
      "main() = foo(@lists:seq(1, 2) : T<Int>) == [2, 4]"
    ))
  , ?_test(48 = Run(
      "interface ToI { to_i : T -> Int }\n"
      "impl ToI for [Int] { to_i([h | _]) = h }\n"
      "foo(x) =\n"
      "  @io:printable_range() : T<A> == x\n"
      "  to_i(x)\n"
      "main() = foo([48, 7, 8])"
    ))


  % to ensure code gen works even with iv unification
  , ?_test({true, $b} = Run(
      "interface Foo { foo : T -> T }\n"
      "interface Bar { bar : T -> T }\n"
      "impl Foo for Atom { foo(a) = a }\n"
      "impl Foo for (A ~ Foo, B) { foo((a, b)) = (foo(a), b) }\n"
      "baz(a, b) =\n"
      "  let x = foo(a)\n"
      "  let y = foo(b)\n"
      "  let same = x == y\n"
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
      "baz(a, b) =\n"
      "  let x = foo(a)\n"
      "  let y = bar(b)\n"
      "  let same = x == y\n"
      "  (same, match x { (@hi, _) => 'a', _ => 'b' })\n"
      "main() = baz((@hi, 3), (@hey, 4))"
    ))


  , ?_test(84 = Run(
      "interface ToI extends Num { to_i : T -> Int }\n"
      "impl ToI for Float { to_i(f) = @erlang:round(f) }"
      "main() = to_i(84.1)"
    ))
  , ?_test({hey, $h, <<"hello">>} = Run(
      "interface First { first : T -> Atom }\n"
      "interface Second extends First { second : T -> Char }\n"
      "interface Third extends Second { third : T -> String }\n"
      "impl First for (Atom, Char, String) { first((f, _, _)) = f }\n"
      "impl Second for (Atom, Char, String) { second((_, s, _)) = s }\n"
      "impl Third for (Atom, Char, String) { third((_, _, t)) = t }\n"
      "foo(x) = (first(x), second(x), third(x))\n"
      "main() = foo((@hey, 'h', \"hello\"))"
    ))
  , ?_test(68 = Run(
      "interface Foo { foo : T -> String }\n"
      "interface ToI extends Base.Concat, Foo { to_i : T -> Int }\n"
      "impl Foo for [A] { foo(_) = \"list\" }\n"
      "impl ToI for [Int] {\n"
      "  to_i(l) = match l { [h | t] => h + to_i(t), [] => 0 }\n"
      "}\n"
      "main() = to_i([17, 48, 3])"
    ))
  , ?_test(381 = Run(
      "interface Foo { foo : T -> Int }\n"
      "interface ToI extends Foo { to_i : T -> Int }\n"
      "impl Foo for String { foo = @erlang:byte_size/1 }\n"
      "impl Foo for [A ~ Foo] { foo([a]) = foo(a) }\n"
      "impl ToI for String {\n"
      "  to_i(s) = foo(s) + @erlang:binary_to_integer(s)\n"
      "}\n"
      "impl ToI for [A ~ ToI] { to_i([a]) = to_i(a) }\n"
      "main() = to_i([\"378\"])"
    ))
  % subtract 1 from map_size to account for tag
  , ?_assertEqual(
      {2, 1, [false, true], #{
        '_@type' => 'Set',
        #{'_@type' => '_@Record', greeting => <<"hi">>} => true
      }},
      Run(
        "interface Collection extends Mappable { len : T<A> -> Int }\n"
        "interface Mappable { map : (A -> B, T<A>) -> T<B> }\n"
        "impl Collection for List { len = @erlang:length/1 }\n"
        "impl Mappable for List { map = @lists:map/2 }\n"
        "impl Collection for Set { len(s) = @erlang:map_size(s) - 1 }\n"
        "impl Mappable for Set {\n"
        "  map(f, s) =\n"
        "    let elems = @maps:keys(@maps:remove(@\"_@type\", s))\n"
        "    let pairs = @lists:map(|e| (f(e), true), elems)\n"
        "    @maps:from_list([(@\"_@type\", @Set) | pairs])\n"
        "}\n"
        "main() =\n"
        "  let l = [1, 2]\n"
        "  let s = #[\"hi\"]\n"
        "  (len(l), len(s), map(|x| x == 2, l), map(|x| { greeting = x }, s))\n"
      )
    )
  ].

code_gen_gen_tv_test_() -> test_gen_tv(fun run_code_gen/1).
interpreter_gen_tv_test_() -> test_gen_tv(fun run_interpreter/1).
test_gen_tv(Run) ->
  [ ?_assertEqual(
      {[1, 2, 3], #{'_@type' => 'Set', hey => true, hi => true}},
      Run(
        "foo : T<A> -> T<A>\n"
        "foo(x) = x\n"
        "main() = (foo([1, 2, 3]), foo(#[@hey, @hi]))"
      )
    )
  , ?_test([1] = Run(
      "foo : T<Int> -> T<Int>\n"
      "foo(x) = x\n"
      "main() = foo([1])"
    ))
  , ?_assertEqual(
      {[1, 2, 3, 1, 2, 3],
       #{'_@type' => 'Set', hey => true, hi => true}},
      Run(
        "foo : T<A> ~ Base.Concat -> T<A> ~ Base.Concat\n"
        "foo(x) = x ++ x\n"
        "main() = (foo([1, 2, 3]), foo(#[@hey, @hi]))"
      )
    )
  , ?_test($a = Run(
      "foo : T<A> -> T<A>\n"
      "foo(x) = x\n"
      "bar(y, z) =\n"
      "  foo(y)\n"
      "  foo(z)\n"
      "  y ++ z\n"
      "  'a'\n"
      "main() = bar({ 3.5 => @hi }, { 4.7 => @hello })"
    ))
  , ?_test([false, false] = Run(
      "foo : T<A> -> T<A>\n"
      "foo(x) = x\n"
      "bar(y, z) =\n"
      "  foo(y)\n"
      "  foo(z)\n"
      "  y ++ z\n"
      "  z ++ []\n"
      "main() = bar([true], [false, false])"
    ))
  , ?_assertEqual(#{hello => 5.1}, Run(
      "foo : (A, T<A>) -> T<A>\n"
      "foo(_, x) = x\n"
      "main() = foo((@hi, 3.7), { @hello => 5.1 })"
    ))
  , ?_test([{hey, $a}] = Run(
      "foo : T<A, B> -> T<A, B>\n"
      "foo(x) = x\n"
      "main() = foo([(@hey, 'a')])"
    ))
  , ?_test(true = Run(
      "foo : T<A> -> T<A>\n"
      "foo(x) = x\n"
      "bar : T<B, C> -> T<B, C>\n"
      "bar(x) = x\n"
      "baz(y, z) =\n"
      "  foo(y)\n"
      "  bar(z)\n"
      "  y == z\n"
      "main() = baz({ @a => 3 }, { @a => 3 })"
    ))
  , ?_test(false = Run(
      "foo : T<A> -> T<A>\n"
      "foo(x) = x\n"
      "bar : T<B, C> -> T<B, C>\n"
      "bar(x) = x\n"
      "baz(y, z) =\n"
      "  foo(y)\n"
      "  bar(z)\n"
      "  y == z\n"
      "  z == { 'c' => true }\n"
      "main() = baz({ 'c' => true }, { 'c' => false })"
    ))
  ].

code_gen_pattern_test_() ->
  test_pattern(fun expr_code_gen/1, fun run_code_gen/1).
interpreter_pattern_test_() ->
  test_pattern(fun expr_interpreter/1, fun run_interpreter/1).
test_pattern(Expr, Run) ->
  [ ?_test(true = Expr("match 3 { 3 => true, 4 => false }"))
  , ?_test(false = Expr("match -4.8 { -3 => true, -4.8 => false }"))
  , ?_test(18 = Expr(
      "let x = 3\n"
      "match x + 5 { a => a + 10 }"
    ))
  , ?_test(hello = Expr("match 'x' { 'y' => @hi, 'x' => @hello }"))
  , ?_test(5.0 = Expr(
      "match |x| x {\n"
      "  id =>\n"
      "    let y = id(true)\n"
      "    id(5.0)\n"
      "}"
    ))
  , ?_test({} = Expr("match () { () => () }"))
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
      "let x = [([], \"hi\", 3.0), ([2, 3], \"hey\", 58.0)]\n"
      "match x {\n"
      "  [([h | t], _, _) | _] => h\n"
      "  [_, ([], _, c)] => c\n"
      "  [(_, _, c), ([x, y | []], _, _)] => c + x - y\n"
      "}"
    ))
  , ?_test([1, 2] = Expr(
      "let (x, y) = (3, [2])\n"
      "match [1] { &y => y ++ [1], x => x ++ [2] }"
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


  , ?_test([] = Expr(
      "let 3 = 3\n"
      "[]"
    ))
  , ?_test({5, 5.0} = Expr(
      "let [_, (x, _, _)] = [(1, \"foo\", @foo), (2, \"bar\", @bar)]\n"
      "(x + 3 : Int, x + 3.0)"
    ))
  , ?_test(7 = Expr(
      "let [_, a] = [1, 3]\n"
      "let (&a, b, &a) = (3, 7, 3)\n"
      "b"
    ))


  , ?_test({} = Expr("if let a = 3.0 then a"))
  % To ensure env is reset appropriately.
  , ?_test(true = Expr(
      "let a = true\n"
      "if let a = 3.0 then a\n"
      "a"
    ))
  , ?_test(true = Expr(
      "let a = true\n"
      "if let a = 3.0 then a else 5\n"
      "a"
    ))
  % Ensure the correct a is used in the else clause. The Erlang compiler
  % will complain if a is unbound.
  , ?_test(3 = Expr("(|a| if let a = a + 1 then a else a)(2)"))
  , ?_test(<<"hey">> = Expr("if let (2, a) = (1, \"hi\") then a else \"hey\""))
  , ?_test(2.5 = Expr(
      "if let f = |b| if b then f(!b) + 1 else 1.5\n"
      "then f(true)\n"
      "else 0"
    ))
  ].

code_gen_assert_test_() -> test_assert(fun expr_code_gen/1).
%% interpreter_assert_test_() -> test_assert(fun expr_interpreter/1).
test_assert(Expr) ->
  [ ?_test(ok = Expr("assert true"))
  , ?_assertError(
      {assert, [
        {expected, true},
        {value, false},
        {expression, "false"},
        {module, 'Mod'},
        {line, 3}
      ]},
      Expr("assert false")
    )
  , ?_test(ok = Expr("assert @hey == @hey"))
  , ?_assertError(
      {assertEqual, [
        {expected, 98},
        {value, 97},
        {expression, "'a' == 'b'"},
        {module, 'Mod'},
        {line, 3}
      ]},
      Expr("assert 'a' == 'b'")
    )
  , ?_test(ok = Expr("assert true != false"))
  , ?_assertError(
      {assertNotEqual, [
        {value, <<>>},
        {expression, "x != \"\""},
        {module, 'Mod'},
        {line, 4}
      ]},
      Expr(
        "let x = \"\"\n"
        "assert x != \"\""
      )
    )
  , ?_test(ok = Expr("assert let 3 = 3"))
  , ?_assertError(
      {assertMatch, [
        {pattern, "3"},
        {value, 4},
        {expression, "4"},
        {module, 'Mod'},
        {line, 3}
      ]},
      Expr("assert let 3 = 4")
    )
  , ?_assertError(
      {badmatch, hi},
      Expr(
        "assert let 3 = 3\n"
        "let @hey = @hi"
      )
    )
  , ?_test(begin
      {3, Fun} = Expr("test assert true"),
      ok = Fun()
    end)
  , ?_assertError(
      {assertMatch, [
        {pattern, "@hello"},
        {value, hey},
        {expression, "x"},
        {module, 'Mod'},
        {line, 4}
      ]},
      begin
        {4, Fun} = Expr(
          "let x = @hey\n"
          "test assert let @hello = x"
        ),
        ok = Fun()
      end
    )
  ].

code_gen_import_test_() -> test_import(fun many_code_gen/2).
% interpreter_import_test_() -> test_import(fun many_interpreter/2).
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
      #{'_@type' => 'Baz', a => 3},
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
      #{'_@type' => 'Baz', a => 3},
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
      #{'_@type' => 'Baz', a => 5},
      Many([
        {"foo", "module Foo struct Baz { a : Int }"},
        {"bar",
          "module Bar\n"
          "import \"./foo\"\n"
          "f(x) = Foo.Baz { a = 5 | x }\n"
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
      {'Baz', #{'_@type' => 'Baz', a => 3}},
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
  , ?_assertEqual(#{'_@type' => 'Baz', a => 3}, Many([
      {"foo", "module Foo struct Baz { a : Int }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\" (Baz)\n"
        "main() = Baz(3)"
      }
    ], "bar"))
  , ?_assertEqual(
      {#{'_@type' => 'Baz', a => 3}, #{'_@type' => 'Baz', a => 4}},
      Many([
        {"foo", "module Foo struct Baz { a : Int }"},
        {"bar",
          "module Bar\n"
          "import \"./foo\" (Baz)\n"
          "x = Baz { a = 3 }\n"
          "y = Baz { a = 4 | { a = 3 } }\n"
          "main() = (x, y)"
        }
      ], "bar")
    )
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
      {"foo", "module Foo enum Foo { One, Two(Bool), Three }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\" (One, Two, Three)\n"
        "f(x) = match x { One => 1, Two(_) => 2, Three => 3 }\n"
        "main() = f(Two(true))"
      }
    ], "bar"))
  , ?_test(3 = Many([
      {"foo", "module Foo enum Foo { One, Two(Bool), Three }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\" (variants Foo)\n"
        "f(x) = match x { One => 1, Two(_) => 2, Three => 3 }\n"
        "main() = f(Three)"
      }
    ], "bar"))
  , ?_assertEqual(#{'_@type' => 'Loc', start_line => 18}, Many([
      {"foo", "module Foo struct Loc { start_line : Int }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\" (Loc)\n"
        "f : Loc -> Loc\n"
        "f(l) = { start_line = l.start_line + 1 }\n"
        "main() = f({ start_line = 17 })"
      }
    ], "bar"))
  , ?_assertEqual({'Baz', #{'_@type' => 'Loc', start_line => 3}}, Many([
      {"foo", "module Foo struct Loc { start_line : Int }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\" (Loc)\n"
        "enum Bar { Baz(Loc) }\n"
        "main() = Baz({ start_line = 3 })"
      }
    ], "bar"))
  , ?_assertEqual(
      {{'Hello', h}, 'Hi', #{'_@type' => 'Baz', first => $f, second => <<"s">>},
       false},
      Many([
        {"foo",
          "module Foo\n"
          "enum Foo { Hello(Atom), Hi }\n"
          "struct Baz { first : Char, second : String }\n"
          "export x = false\n"
          "y = 3.7\n"
        },
        {"bar",
          "module Bar\n"
          "import \"./foo\" (*)\n"
          "main : () -> (Foo, Foo, Baz, Bool)\n"
          "main() = (Hello(@h), Hi, Baz { first = 'f', second = \"s\" }, x)"
        }
      ], "bar")
    )


  , ?_assertEqual($a + $b, Many([
      {"foo",
        "module Foo\n"
        "interface ToI { to_i : T -> Int }\n"
        "impl ToI for Char { to_i(c) = $c }\n"
        "impl ToI for (A ~ ToI, B ~ ToI) {\n"
        "  to_i((a, b)) = to_i(a) + to_i(b)\n"
        "}"
      },
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "main() = Foo.to_i(('a', 'b'))"
      }
    ], "bar"))
  , ?_assertEqual($a + $b, Many([
      {"foo", "module Foo interface ToI { to_i : T -> Int }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "impl Foo.ToI for Char { to_i(c) = $c }\n"
        "impl Foo.ToI for (A ~ Foo.ToI, B ~ Foo.ToI) {\n"
        "  to_i((a, b)) = Foo.to_i(a) + Foo.to_i(b)\n"
        "}\n"
        "main() = Foo.to_i(('a', 'b'))"
      }
    ], "bar"))
  , ?_assertEqual($a + $b, Many([
      {"foo",
        "module Foo\n"
        "interface ToI { to_i : T -> Int }\n"
        "impl ToI for Char { to_i(c) = $c }"
      },
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "impl Foo.ToI for (A ~ Foo.ToI, B ~ Foo.ToI) {\n"
        "  to_i((a, b)) = Foo.to_i(a) + Foo.to_i(b)\n"
        "}\n"
        "main() = Foo.to_i(('a', 'b'))"
      }
    ], "bar"))
  , ?_assertEqual($a + $b, Many([
      {"foo",
        "module Foo\n"
        "interface ToI { to_i : T -> Int }\n"
        "impl ToI for (A ~ ToI, B ~ ToI) {\n"
        "  to_i((a, b)) = to_i(a) + to_i(b)\n"
        "}"
      },
      {"bar",
        "module Bar\n"
        "import \"./foo\"\n"
        "impl Foo.ToI for Char { to_i(c) = $c }\n"
        "main() = Foo.to_i(('a', 'b'))"
      }
    ], "bar"))
  , ?_assertEqual($a + $b, Many([
      {"foo", "module Foo interface ToI { to_i : T -> Int }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\" (ToI)\n"
        "impl ToI for Char { to_i(c) = $c }\n"
        "impl ToI for (A ~ ToI, B ~ ToI) {\n"
        "  to_i((a, b)) = Foo.to_i(a) + Foo.to_i(b)\n"
        "}\n"
        "main() = Foo.to_i(('a', 'b'))"
      }
    ], "bar"))
  , ?_assertEqual($a + $b, Many([
      {"foo", "module Foo interface ToI { to_i : T -> Int }"},
      {"bar",
        "module Bar\n"
        "import \"./foo\" (ToI, to_i)\n"
        "impl ToI for Char { to_i(c) = $c }\n"
        "impl ToI for (A ~ ToI, B ~ ToI) {\n"
        "  to_i((a, b)) = to_i(a) + to_i(b)\n"
        "}\n"
        "main() = to_i(('a', 'b'))"
      }
    ], "bar"))
  ].
