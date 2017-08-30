-module(parser_test).
-export([ok_prg/1, ok_expr/1]).
-on_load(load/0).

-include_lib("eunit/include/eunit.hrl").
-define(DEF_PREFIX, "module Mod\n").
-define(EXPR_PREFIX, "module Mod expr =\n").

load() -> 'Parser':'_@init'(gb_sets:new()).

ok_prg(Prg) ->
  {ok, Tokens} = 'Lexer':tokenize(Prg),
  #{value := {some, Ast}, errs := []} = 'Parser':parse(Tokens),
  rewrite_refs(Ast).

ok_prefix(Prefix, Prg) ->
  Ast = ok_prg(Prefix ++ Prg),
  % l() assumes we're starting after the module line, but we're testing the
  % module line itself, so pass -1
  ModuleLoc = l(-1, 0, 10),
  ConLoc = l(-1, 7, 3),

  {module, ModuleLoc, {con_token, ConLoc, "Mod"}, [], Defs} = Ast,
  [Def] = Defs,
  Def.

ok_def(Prg) -> ok_prefix(?DEF_PREFIX, Prg).

ok_expr(Expr) ->
  VarLoc = l(-1, 11, 4),
  Lines = re:split(Expr, "\n", [{return, list}]),
  GlobalLoc = l(-1, 11, length(Lines) - 1, length(lists:last(Lines))),

  Def = ok_prefix(?EXPR_PREFIX, Expr),
  {global, GlobalLoc, {var, VarLoc, "expr"}, Parsed, false} = Def,
  Parsed.

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

rewrite_refs(V) when is_list(V) -> lists:map(fun rewrite_refs/1, V);
rewrite_refs({anon_record, Loc, _, Inits}) ->
  {anon_record, Loc, ref, rewrite_refs(Inits)};
rewrite_refs({anon_record_ext, Loc, _, Expr, AllInits}) ->
  {anon_record_ext, Loc, ref, rewrite_refs(Expr), rewrite_refs(AllInits)};
rewrite_refs(V) when is_tuple(V) ->
  list_to_tuple(rewrite_refs(tuple_to_list(V)));
rewrite_refs(V) -> V.

expr_test_() ->
  [ ?_assertEqual({unit, l(0, 2)}, ok_expr("()"))
  , ?_assertEqual({int, l(0, 1), 1}, ok_expr("1"))
  , ?_assertEqual({int, l(0, 3), 517}, ok_expr("517"))
  , ?_assertEqual({float, l(0, 3), 1.0}, ok_expr("1.0"))
  , ?_assertEqual({float, l(0, 5), 0.517}, ok_expr("0.517"))
  , ?_assertEqual({float, l(0, 2), 0.3}, ok_expr(".3"))
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


  , ?_assertEqual({list, l(0, 2), []}, ok_expr("[]"))
  , ?_assertEqual(
      {list, l(0, 11), [
        {int, l(1, 1), 3},
        {float, l(4, 3), 5.0},
        {int, l(9, 1), 6}
      ]},
      ok_expr("[3, 5.0, 6]")
    )
  , ?_assertEqual(
      {list, l(0, 23), [
        {list, l(1, 10), [
          {atom, l(2, 2), a},
          {atom, l(6, 4), hey}
        ]},
        {list, l(13, 2), []},
        {list, l(17, 5), [{atom, l(18, 3), hi}]}
      ]},
      ok_expr("[[@a, @hey], [], [@hi]]")
    )
  , ?_assertEqual({list, l(0, 6), [{bool, l(1, 4), true}]}, ok_expr("[true]"))
  , ?_assertEqual(
      {list, l(0, 7), [{var, l(1, 1), "a"}, {var, l(4, 1), "b"}]},
      ok_expr("[a, b,]")
    )


  , ?_assertEqual({bool, l(0, 6), true}, ok_expr("(true)"))
  , ?_assertEqual(
      {tuple, l(0, 12), [
        {bool, l(1, 5), false},
        {float, l(8, 3), 3.0}
      ]},
      ok_expr("(false, 3.0)")
    )
  , ?_assertEqual(
      {tuple, l(0, 13), [
        {bool, l(1, 5), false},
        {float, l(8, 3), 3.0}
      ]},
      ok_expr("(false, 3.0,)")
    )
  , ?_assertEqual(
      {tuple, l(0, 21), [
        {int, l(1, 1), 1},
        {str, l(4, 4), <<"hi">>},
        {list, l(10, 10), [
          {atom, l(11, 2), a},
          {atom, l(15, 4), hey}
        ]}
      ]},
      ok_expr("(1, \"hi\", [@a, @hey])")
    )
  , ?_assertEqual(
      {tuple, l(0, 18), [
        {tuple, l(1, 10), [
          {int, l(2, 1), 3},
          {bool, l(5, 5), false}
        ]},
        {float, l(13, 4), 4.01}
      ]},
      ok_expr("((3, false), 4.01)")
    )
  , ?_assertEqual(
      {tuple, l(0, 18), [
        {char, l(1, 3), $c},
        {tuple, l(6, 11), [
          {str, l(7, 2), <<"">>},
          {atom, l(11, 5), yeah}
        ]}
      ]},
      ok_expr("('c', (\"\", @yeah))")
    )


  , ?_assertEqual({map, l(0, 2), []}, ok_expr("{}"))
  , ?_assertEqual(
      {map, l(0, 12), [{{str, l(1, 5), <<"key">>}, {int, l(10, 1), 3}}]},
      ok_expr("{\"key\" => 3}")
    )
  , ?_assertEqual(
      {map, l(0, 34), [
        {{atom, l(1, 3), hi}, {map, l(8, 2), []}},
        {{atom, l(12, 4), hey}, {map, l(20, 13), [
          {{bool, l(21, 4), true}, {float, l(29, 3), 4.0}}
        ]}}
      ]},
      ok_expr("{@hi => {}, @hey => {true => 4.0}}")
    )
  , ?_assertEqual(
      {map, l(0, 0, 3, 1), [
        {{atom, l(1, 2, 2), a}, {atom, l(1, 8, 2), b}},
        {{atom, l(2, 2, 2), c}, {atom, l(2, 8, 2), d}}
      ]},
      ok_expr(
        "{\n"
        "  @a => @b,\n"
        "  @c => @d,\n"
        "}"
      )
    )


  , ?_assertEqual(
      {anon_record, l(0, 9), ref, [
        {init, l(2, 5), {var, l(2, 1), "a"}, {int, l(6, 1), 3}}
      ]},
      ok_expr("{ a = 3 }")
    )
  , ?_assertEqual(
      {anon_record, l(0, 12), ref, [
        {init, l(2, 8), {var, l(2, 1), "f"},
          {fn, l(2, 8), [{var, l(4, 1), "x"}], {int, l(9, 1), 3}}}
      ]},
      ok_expr("{ f(x) = 3 }")
    )
  , ?_assertEqual(
      {anon_record, l(0, 21), ref, [
        {init, l(2, 5), {var, l(2, 1), "a"}, {int, l(6, 1), 3}},
        {init, l(9, 10), {var, l(9, 3), "bar"}, {bool, l(15, 4), true}}
      ]},
      ok_expr("{ a = 3, bar = true }")
    )
  , ?_assertEqual(
      {anon_record, l(0, 24), ref, [
        {init, l(2, 8), {var, l(2, 1), "f"},
          {fn, l(2, 8), [{var, l(4, 1), "x"}], {int, l(9, 1), 3}}},
        {init, l(12, 10), {var, l(12, 3), "bar"}, {bool, l(18, 4), true}}
      ]},
      ok_expr("{ f(x) = 3, bar = true }")
    )
  , ?_assertEqual(
      {anon_record, l(0, 0, 1, 12), ref, [
        {init, l(2, 5), {var, l(2, 1), "a"}, {int, l(6, 1), 3}},
        {init, l(1, 0, 10), {var, l(1, 0, 3), "bar"}, {bool, l(1, 6, 4), true}}
      ]},
      ok_expr("{ a = 3\nbar = true }")
    )
  , ?_assertEqual(
      {record, l(0, 13), {con_token, l(0, 3), "Foo"}, [
        {init, l(6, 5), {var, l(6, 1), "a"}, {int, l(10, 1), 3}}
      ]},
      ok_expr("Foo { a = 3 }")
    )
  , ?_assertEqual(
      {record, l(0, 25), {con_token, l(0, 3), "Foo"}, [
        {init, l(6, 5), {var, l(6, 1), "a"}, {int, l(10, 1), 3}},
        {init, l(13, 10), {var, l(13, 3), "bar"}, {bool, l(19, 4), true}}
      ]},
      ok_expr("Foo { a = 3, bar = true }")
    )
  , ?_assertEqual(
      {record, l(0, 0, 1, 12), {con_token, l(0, 3), "Foo"}, [
        {init, l(6, 5), {var, l(6, 1), "a"}, {int, l(10, 1), 3}},
        {init, l(1, 0, 10), {var, l(1, 0, 3), "bar"}, {bool, l(1, 6, 4), true}}
      ]},
      ok_expr("Foo { a = 3\nbar = true }")
    )
  , ?_assertEqual(
      {record, l(0, 32), {con_token, l(0, 10), "Module.Foo"}, [
        {init, l(13, 5), {var, l(13, 1), "a"}, {int, l(17, 1), 3}},
        {init, l(20, 10), {var, l(20, 3), "bar"}, {bool, l(26, 4), true}}
      ]},
      ok_expr("Module.Foo { a = 3, bar = true }")
    )
  % to ensure parsing after named record works fine
  , ?_assertEqual(
      {binary_op, l(0, 18), '==',
        {record, l(0, 13), {con_token, l(0, 3), "Foo"}, [
          {init, l(6, 5), {var, l(6, 1), "a"}, {int, l(10, 1), 3}}
        ]},
        {int, l(17, 1), 1}
      },
      ok_expr("Foo { a = 3 } == 1")
    )


  , ?_assertEqual(
      {anon_record_ext, l(0, 21), ref,
        {anon_record, l(2, 9), ref, [
          {init, l(4, 5), {var, l(4, 1), "a"}, {int, l(8, 1), 3}}
        ]},
        [{init, l(14, 5), {var, l(14, 1), "a"}, {int, l(18, 1), 4}}]
      },
      ok_expr("{ { a = 3 } | a = 4 }")
    )
  , ?_assertEqual(
      {anon_record_ext, l(0, 27), ref, {var, l(2, 1), "a"}, [
        {init, l(6, 8), {var, l(6, 3), "bar"}, {atom, l(12, 2), a}},
        {ext, l(16, 9), {var, l(16, 1), "c"}, {bool, l(21, 4), true}}
      ]},
      ok_expr("{ a | bar = @a, c := true }")
    )
  , ?_assertEqual(
      {anon_record_ext, l(0, 34), ref, {var, l(2, 1), "a"}, [
        {init, l(6, 8), {var, l(6, 1), "f"},
          {fn, l(6, 8), [], {atom, l(12, 2), a}}},
        {ext, l(16, 16), {var, l(16, 1), "c"},
          {fn, l(16, 16),
            [{var, l(18, 1), "x"}, {var, l(21, 1), "y"}],
            {binary_op, l(27, 5), '+',
              {var, l(27, 1), "x"},
              {var, l(31, 1), "y"}
            }
          }
        }
      ]},
      ok_expr("{ a | f() = @a, c(x, y) := x + y }")
    )
  , ?_assertEqual(
      {anon_record_ext, l(0, 0, 1, 11), ref, {var, l(2, 1), "a"}, [
        {init, l(6, 8), {var, l(6, 3), "bar"}, {atom, l(12, 2), a}},
        {ext, l(1, 0, 9), {var, l(1, 0, 1), "c"}, {bool, l(1, 5, 4), true}}
      ]},
      ok_expr("{ a | bar = @a\nc := true }")
    )
  , ?_assertEqual(
      {record_ext, l(0, 31),
        {con_token, l(0, 3), "Foo"},
        {var, l(6, 1), "a"}, [
          {init, l(10, 8), {var, l(10, 3), "bar"}, {atom, l(16, 2), a}},
          {ext, l(20, 9), {var, l(20, 1), "c"}, {bool, l(25, 4), true}}
        ]
      },
      ok_expr("Foo { a | bar = @a, c := true }")
    )
  , ?_assertEqual(
      {record_ext, l(0, 0, 1, 11),
        {con_token, l(0, 3), "Foo"},
        {var, l(6, 1), "a"}, [
          {init, l(10, 8), {var, l(10, 3), "bar"}, {atom, l(16, 2), a}},
          {ext, l(1, 0, 9), {var, l(1, 0, 1), "c"}, {bool, l(1, 5, 4), true}}
        ]
      },
      ok_expr("Foo { a | bar = @a\nc := true }")
    )


  , ?_assertEqual(
      {field_fn, l(0, 4), {var, l(1, 3), "bar"}},
      ok_expr(".bar")
    )
  , ?_assertEqual(
      {field, l(0, 5), {var, l(0, 1), "a"}, {var, l(2, 3), "bar"}},
      ok_expr("a.bar")
    )
  , ?_assertEqual(
      {app, l(0, 24),
        {field, l(0, 21),
          {anon_record, l(0, 17), ref, [
            {init, l(2, 13),
              {var, l(2, 3), "bar"},
              {fn, l(8, 7), [{var, l(9, 1), "x"}], {atom, l(12, 3), hi}}
            }
          ]},
          {var, l(18, 3), "bar"}
        },
        [{int, l(22, 1), 2}]
      },
      ok_expr("{ bar = |x| @hi }.bar(2)")
    )


  , ?_assertEqual(
      {binary_op, l(0, 6), '==', {int, l(0, 1), 1}, {int, l(5, 1), 2}},
      ok_expr("1 == 2")
    )
  , ?_assertEqual(
      {binary_op, l(0, 13), '!=',
        {bool, l(0, 4), true},
        {bool, l(8, 5), false}
      },
      ok_expr("true != false")
    )


  , ?_assertEqual(
      {binary_op, l(0, 13), '||',
        {bool, l(0, 5), false},
        {bool, l(9, 4), true}
      },
      ok_expr("false || true")
    )
  , ?_assertEqual(
      {binary_op, l(0, 13), '&&',
        {bool, l(0, 4), true},
        {bool, l(8, 5), false}
      },
      ok_expr("true && false")
    )


  , ?_assertEqual(
      {binary_op, l(0, 6), '>', {int, l(0, 2), 10}, {int, l(5, 1), 2}},
      ok_expr("10 > 2")
    )
  , ?_assertEqual(
      {binary_op, l(0, 9), '>=', {float, l(0, 3), 3.0}, {float, l(7, 2), 0.4}},
      ok_expr("3.0 >= .4")
    )
  , ?_assertEqual(
      {binary_op, l(0, 7), '<', {float, l(0, 3), 3.0}, {int, l(6, 1), 4}},
      ok_expr("3.0 < 4")
    )
  , ?_assertEqual(
      {binary_op, l(0, 9), '<=', {int, l(0, 2), 10}, {float, l(6, 3), 2.0}},
      ok_expr("10 <= 2.0")
    )


  , ?_assertEqual(
      {binary_op, l(0, 10), '+', {int, l(0, 3), 100}, {float, l(6, 4), 50.0}},
      ok_expr("100 + 50.0")
    )
  , ?_assertEqual(
      {binary_op, l(0, 9), '-', {float, l(0, 5), 35.27}, {int, l(8, 1), 1}},
      ok_expr("35.27 - 1")
    )
  , ?_assertEqual(
      {binary_op, l(0, 11), '*',
        {float, l(0, 4), 35.2},
        {float, l(7, 4), 1.38}
      },
      ok_expr("35.2 * 1.38")
    )
  , ?_assertEqual(
      {binary_op, l(0, 6), '/', {int, l(0, 2), 35}, {int, l(5, 1), 2}},
      ok_expr("35 / 2")
    )
  , ?_assertEqual(
      {binary_op, l(0, 8), '%', {int, l(0, 3), 210}, {int, l(6, 2), 17}},
      ok_expr("210 % 17")
    )


  % - and + are left-associative
  , ?_assertEqual(
      {binary_op, l(0, 13), '+',
        {binary_op, l(0, 9), '-',
          {binary_op, l(0, 5), '-',
            {int, l(0, 1), 3},
            {int, l(4, 1), 2}
          },
          {int, l(8, 1), 1}
        },
        {int, l(12, 1), 4}
      },
      ok_expr("3 - 2 - 1 + 4")
    )


  , ?_assertEqual(
      {binary_op, l(0, 33), '+',
        {binary_op, l(0, 27), '-',
          {binary_op, l(0, 18), '+',
            {int, l(0, 1), 3},
            {binary_op, l(4, 14), '/',
              {binary_op, l(4, 7), '*',
                {float, l(4, 3), 5.8},
                {int, l(10, 1), 7}
              },
              {float, l(14, 4), 2.31}
            }
          },
          {binary_op, l(21, 6), '%',
            {int, l(21, 2), 38},
            {int, l(26, 1), 6}
          }
        },
        {float, l(30, 3), 8.2}
      },
      ok_expr("3 + 5.8 * 7 / 2.31 - 38 % 6 + 8.2")
    )


  , ?_assertEqual(
      {cons, l(0, 10), [{float, l(1, 3), 3.0}], {list, l(7, 2), []}},
      ok_expr("[3.0 | []]")
    )
  , ?_assertEqual(
      {cons, l(0, 20),
        [{atom, l(1, 2), a}],
        {list, l(6, 13), [
          {atom, l(7, 4), bar},
          {atom, l(13, 5), call}
        ]}
      },
      ok_expr("[@a | [@bar, @call]]")
    )
  , ?_assertEqual(
      {cons, l(0, 19),
        [{char, l(1, 3), $a}, {char, l(6, 4), $\n}],
        {list, l(13, 5), [{char, l(14, 3), $b}]}
      },
      ok_expr("['a', '\\n' | ['b']]")
    )


  , ?_assertEqual(
      {binary_op, l(0, 15), '++',
        {list, l(0, 6), [
          {int, l(1, 1), 1},
          {int, l(4, 1), 2}
        ]},
        {list, l(10, 5), [{float, l(11, 3), 3.0}]}
      },
      ok_expr("[1, 2] ++ [3.0]")
    )
  , ?_assertEqual(
      {binary_op, l(0, 15), '--',
        {list, l(0, 6), [{atom, l(1, 4), hey}]},
        {list, l(10, 5), [{atom, l(11, 3), hi}]}
      },
      ok_expr("[@hey] -- [@hi]")
    )


  , ?_assertEqual(
      {unary_op, l(0, 3), '#', {list, l(1, 2), []}},
      ok_expr("#[]")
    )
  , ?_assertEqual(
      {unary_op, l(0, 7), '#', {list, l(1, 6), [
        {int, l(2, 1), 1},
        {int, l(5, 1), 2}
      ]}},
      ok_expr("#[1, 2]")
    )
  , ?_assertEqual(
      {unary_op, l(0, 4), '#', {atom, l(1, 3), hi}},
      ok_expr("#@hi")
    )
  , ?_assertEqual(
      {unary_op, l(0, 3), '-', {int, l(1, 2), 15}},
      ok_expr("-15")
    )
  , ?_assertEqual(
      {unary_op, l(0, 6), '!', {bool, l(1, 5), false}},
      ok_expr("!false"))
  , ?_assertEqual(
      {unary_op, l(0, 4), '$', {char, l(1, 3), $h}},
      ok_expr("$'h'")
    )
  , ?_assertEqual(
      {unary_op, l(0, 11), 'discard', {float, l(8, 3), 3.7}},
      ok_expr("discard 3.7")
    )


  , ?_assertEqual(
      {binary_op, l(0, 12), '-',
        {int, l(0, 1), 7},
        {binary_op, l(4, 8), '+',
          {int, l(5, 1), 3},
          {unary_op, l(9, 2), '-', {int, l(10, 1), 5}}
        }
      },
      ok_expr("7 - (3 + -5)")
    )
  , ?_assertEqual(
      {binary_op, l(0, 46), '||',
        {binary_op, l(0, 28), '||',
          {binary_op, l(0, 8), '==',
            {int, l(0, 1), 7},
            {float, l(5, 3), 5.0}
          },
          {binary_op, l(12, 16), '&&',
            {unary_op, l(12, 5), '!', {bool, l(13, 4), true}},
            {binary_op, l(21, 7), '==',
              {unary_op, l(21, 2), '-', {int, l(22, 1), 8}},
              {int, l(27, 1), 3}
            }
          }
        },
        {binary_op, l(32, 14), '!=',
          {bool, l(32, 5), false},
          {bool, l(41, 5), false}
        }
      },
      ok_expr("7 == 5.0 || !true && -8 == 3 || false != false")
    )


  , ?_assertEqual(
      {binary_op, l(0, 9), '|>',
        {atom, l(0, 2), a},
        {var, l(6, 3), "foo"}
      },
      ok_expr("@a |> foo")
    )
  , ?_assertEqual(
      {binary_op, l(0, 27), '|>',
        {int, l(0, 1), 5},
        {fn, l(5, 22), [{var, l(6, 1), "x"}],
          {binary_op, l(9, 18), '|>',
            {binary_op, l(9, 5), '*',
              {int, l(9, 1), 2},
              {var, l(13, 1), "x"}
            },
            {binary_op, l(18, 9), '*',
              {var, l(18, 3), "inc"},
              {float, l(24, 3), 7.5}
            }
          }
        }
      },
      ok_expr("5 |> |x| 2 * x |> inc * 7.5")
    )


  , ?_assertEqual(
      {fn, l(0, 5), [], {int, l(4, 1), 3}},
      ok_expr("|-| 3")
    )
  , ?_assertEqual(
      {fn, l(0, 5), [{var, l(1, 1), "x"}], {var, l(4, 1), "x"}},
      ok_expr("|x| x")
    )
  , ?_assertEqual(
      {fn, l(0, 16), [
          {tuple, l(1, 9), [
            {var, l(2, 4), "left"},
            {'_', l(8, 1)}
          ]}
        ],
        {var, l(12, 4), "left"}
      },
      ok_expr("|(left, _)| left")
    )
  , ?_assertEqual(
      {app, l(0, 25),
        {fn, l(0, 18), [
            {var, l(2, 1), "x"},
            {cons, l(5, 7), [{int, l(6, 1), 3}], {var, l(10, 1), "t"}}
          ],
          {app, l(14, 3), {var, l(14, 1), "x"}, [{unit, l(15, 2)}]}
        },
        [{fn, l(19, 5), [], {int, l(23, 1), 2}}]
      },
      ok_expr("(|x, [3 | t]| x())(|-| 2)")
    )
  , ?_assertEqual(
      {fn, l(0, 13), [{var, l(1, 1), "x"}],
        {fn, l(4, 9), [{var, l(5, 1), "y"}],
          {binary_op, l(8, 5), '+',
            {var, l(8, 1), "x"},
            {var, l(12, 1), "y"}
          }
        }
      },
      ok_expr("|x| |y| x + y")
    )


  , ?_assertEqual(
      {native, l(0, 15),
        {atom, l(0, 6), lists},
        {var, l(7, 6), "filter"},
        2
      },
      ok_expr("@lists:filter/2")
    )
  , ?_assertEqual(
      {app, l(0, 24),
        {native, l(0, 13),
          {atom, l(0, 6), lists},
          {var, l(7, 6), "filter"},
          2
        },
        [{fn, l(14, 5), [{var, l(15, 1), "x"}], {var, l(18, 1), "x"}},
         {list, l(21, 2), []}]
      },
      ok_expr("@lists:filter(|x| x, [])")
    )
  , ?_assertEqual(
      {app, l(0, 31),
        {native, l(0, 21),
          {atom, l(0, 3), io},
          {var, l(4, 15), "printable_range"},
          0
        },
        [{unit, l(22, 2)}, {int, l(26, 1), 1}, {int, l(29, 1), 2}]
      },
      ok_expr("@io:printable_range/0((), 1, 2)")
    )
  % TODO: error case w/ no arity


  , ?_assertEqual(
      {binary_op, l(0, 7), ':', {unit, l(0, 2)}, {unit, l(5, 2)}},
      ok_expr("() : ()")
    )
  , ?_assertEqual(
      {binary_op, l(0, 11), ':',
        {bool, l(0, 4), true},
        {con_token, l(7, 4), "Bool"}
      },
      ok_expr("true : Bool")
    )
  , ?_assertEqual(
      {binary_op, l(0, 17), ':',
        {bool, l(0, 4), true},
        {con_token, l(7, 10), "Module.Foo"}
      },
      ok_expr("true : Module.Foo")
    )
  , ?_assertEqual(
      {binary_op, l(0, 5), ':',
        {int, l(0, 1), 1},
        {tv_te, l(4, 1), "A", none}
      },
      ok_expr("1 : A")
    )
  , ?_assertEqual(
      {binary_op, l(0, 10), ':',
        {int, l(0, 1), 1},
        {tv_te, l(4, 6), "A", {some, {con_token, l(7, 3), "Num"}}}
      },
      ok_expr("1 : A: Num")
    )
  , ?_assertEqual(
      {binary_op, l(0, 17), ':',
        {int, l(0, 1), 1},
        {tv_te, l(4, 13), "A", {some, {con_token, l(7, 10), "Module.Foo"}}}
      },
      ok_expr("1 : A: Module.Foo")
    )
  , ?_assertEqual(
      {binary_op, l(0, 8), ':',
        {list, l(0, 2), []},
        {gen_te, l(5, 3), {con_token, l(5, 3), "List"}, [
          {tv_te, l(6, 1), "A", none}
        ]}
      },
      ok_expr("[] : [A]")
    )
  , ?_assertEqual(
      {binary_op, l(0, 19), ':',
        {unary_op, l(0, 7), '#', {list, l(1, 6), [{bool, l(2, 4), true}]}},
        {gen_te, l(10, 9), {con_token, l(10, 3), "Set"}, [
          {con_token, l(14, 4), "Bool"}
        ]}
      },
      ok_expr("#[true] : Set<Bool>")
    )
  , ?_assertEqual(
      {binary_op, l(0, 25), ':',
        {unary_op, l(0, 7), '#', {list, l(1, 6), [{bool, l(2, 4), true}]}},
        {gen_te, l(10, 15), {con_token, l(10, 9), "Other.Bar"}, [
          {con_token, l(20, 4), "Bool"}
        ]}
      },
      ok_expr("#[true] : Other.Bar<Bool>")
    )
  , ?_assertEqual(
      {binary_op, l(0, 36), ':',
        {map, l(0, 9), [{{atom, l(1, 2), a}, {int, l(7, 1), 3}}]},
        {gen_te, l(12, 24), {con_token, l(12, 3), "Map"}, [
          {con_token, l(16, 4), "Atom"},
          {tv_te, l(22, 13), "A", {some, {con_token, l(25, 10), "Concatable"}}}
        ]}
      },
      ok_expr("{@a => 3} : Map<Atom, A: Concatable>")
    )
  , ?_assertEqual(
      {binary_op, l(0, 9), ':',
        {unit, l(0, 2)},
        {gen_te, l(5, 4), {tv_te, l(5, 4), "T", none}, [
          {tv_te, l(7, 1), "A", none}
        ]}
      },
      ok_expr("() : T<A>")
    )
  , ?_assertEqual(
      {binary_op, l(0, 24), ':',
        {unit, l(0, 2)},
        {gen_te, l(5, 19),
          {tv_te, l(5, 19), "T", {some, {con_token, l(16, 8), "Mappable"}}}, [
            {tv_te, l(7, 1), "A", none},
            {con_token, l(10, 3), "Int"}
          ]
        }
      },
      ok_expr("() : T<A, Int>: Mappable")
    )
  , ?_assertEqual(
      {binary_op, l(0, 26), ':',
        {tuple, l(0, 12), [{atom, l(1, 4), hey}, {str, l(7, 4), <<"hi">>}]},
        {tuple_te, l(15, 11), [
          {tv_te, l(16, 1), "A", none},
          {con_token, l(19, 6), "String"}
        ]}
      },
      ok_expr("(@hey, \"hi\") : (A, String)")
    )
  , ?_assertEqual(
      {binary_op, l(0, 17), ':',
        {char, l(0, 3), $c},
        {lam_te, l(6, 11),
          {con_token, l(6, 6), "String"},
          {tv_te, l(16, 1), "A", none}
        }
      },
      ok_expr("'c' : String -> A")
    )
  % -> is right associative
  , ?_assertEqual(
      {binary_op, l(0, 36), ':',
        {char, l(0, 3), $c},
        {lam_te, l(6, 30),
          {lam_te, l(6, 15),
            {con_token, l(7, 3), "Int"},
            {con_token, l(14, 6), "String"}
          },
          {lam_te, l(25, 11),
            {tv_te, l(25, 6), "A", {some, {con_token, l(28, 3), "Num"}}},
            {tv_te, l(35, 1), "B", none}
          }
        }
      },
      ok_expr("'c' : (Int -> String) -> A: Num -> B")
    )
  , ?_assertEqual(
      {binary_op, l(0, 17), ':',
        {unit, l(0, 2)},
        {record_te, l(5, 12), [
          {sig, l(7, 8), {var, l(7, 1), "a"}, {con_token, l(11, 4), "Bool"}}
        ]}
      },
      ok_expr("() : { a : Bool }")
    )
  , ?_assertEqual(
      {binary_op, l(0, 21), ':',
        {unit, l(0, 2)},
        {record_ext_te, l(5, 16), {tv_te, l(7, 1), "A", none}, [
          {sig, l(11, 8), {var, l(11, 1), "a"}, {con_token, l(15, 4), "Bool"}}
        ]}
      },
      ok_expr("() : { A | a : Bool }")
    )
  , ?_assertEqual(
      {binary_op, l(0, 28), ':',
        {unit, l(0, 2)},
        {record_te, l(5, 23), [
          {sig, l(7, 10),
            {var, l(7, 3), "foo"},
            {con_token, l(13, 4), "Atom"}
          },
          {sig, l(19, 7),
            {var, l(19, 3), "bar"},
            {tv_te, l(25, 1), "A", none}
          }
        ]}
      },
      ok_expr("() : { foo : Atom, bar : A }")
    )
  , ?_assertEqual(
      {binary_op, l(0, 0, 1, 9), ':',
        {unit, l(0, 2)},
        {record_te, l(0, 5, 1, 9), [
          {sig, l(7, 10),
            {var, l(7, 3), "foo"},
            {con_token, l(13, 4), "Atom"}
          },
          {sig, l(1, 0, 7),
            {var, l(1, 0, 3), "bar"},
            {tv_te, l(1, 6, 1), "A", none}
          }
        ]}
      },
      ok_expr("() : { foo : Atom\nbar : A }")
    )
  , ?_assertEqual(
      {binary_op, l(0, 32), ':',
        {unit, l(0, 2)},
        {record_ext_te, l(5, 27), {tv_te, l(7, 1), "B", none}, [
          {sig, l(11, 10),
            {var, l(11, 3), "foo"},
            {con_token, l(17, 4), "Atom"}
          },
          {sig, l(23, 7),
            {var, l(23, 3), "bar"},
            {tv_te, l(29, 1), "A", none}
          }
        ]}
      },
      ok_expr("() : { B | foo : Atom, bar : A }")
    )
  , ?_assertEqual(
      {binary_op, l(0, 0, 1, 9), ':',
        {unit, l(0, 2)},
        {record_ext_te, l(0, 5, 1, 9),
          {tv_te, l(7, 1), "B", none}, [
            {sig, l(11, 10),
              {var, l(11, 3), "foo"},
              {con_token, l(17, 4), "Atom"}
            },
            {sig, l(1, 0, 7),
              {var, l(1, 0, 3), "bar"},
              {tv_te, l(1, 6, 1), "A", none}
            }
          ]
        }
      },
      ok_expr("() : { B | foo : Atom\nbar : A }")
    )


  , ?_assertEqual(
      {'if', l(0, 23),
        {binary_op, l(3, 6), '==',
          {int, l(3, 1), 3},
          {int, l(8, 1), 5}
        },
        {int, l(15, 1), 3},
        {int, l(22, 1), 5}
      },
      ok_expr("if 3 == 5 then 3 else 5")
    )
  , ?_assertEqual(
      {'if', l(0, 17),
        {bool, l(3, 4), true},
        {atom, l(13, 4), foo},
        {unit, l(13, 4)}
      },
      ok_expr("if true then @foo")
    )
  % else binds with closest if
  , ?_assertEqual(
      {'if', l(0, 40),
        {bool, l(3, 4), true},
        {'if', l(13, 27),
          {bool, l(16, 5), false},
          {float, l(27, 3), 5.7},
          {atom, l(36, 4), foo}
        },
        {unit, l(13, 27)}
      },
      ok_expr("if true then if false then 5.7 else @foo")
    )


  , ?_assertEqual(
      {'let', l(0, 20),
        [{binding, l(4, 7), {var, l(4, 1), "x"}, {float, l(8, 3), 3.0}}],
        {binary_op, l(15, 5), '+',
          {var, l(15, 1), "x"},
          {int, l(19, 1), 5}
        }
      },
      ok_expr("let x = 3.0 in x + 5")
    )
  , ?_assertEqual(
      {'let', l(0, 39),
        [{binding, l(4, 7),
           {var, l(4, 1), "f"},
           {fn, l(4, 7), [], {int, l(10, 1), 3}}
         },
         {binding, l(13, 14),
           {var, l(13, 3), "inc"},
           {fn, l(13, 14), [{var, l(17, 1), "x"}],
           {binary_op, l(22, 5), '+',
             {var, l(22, 1), "x"},
             {int, l(26, 1), 1}
           }
         }}],
        {app, l(31, 8),
          {var, l(31, 3), "inc"},
          [{app, l(35, 3), {var, l(35, 1), "f"}, [{unit, l(36, 2)}]}]
        }
      },
      ok_expr("let f() = 3, inc(x) = x + 1 in inc(f())")
    )
  , ?_assertEqual(
      {'let', l(0, 0, 1, 10),
        [{binding, l(4, 7),
           {var, l(4, 1), "f"},
           {fn, l(4, 7), [], {var, l(10, 1), "x"}}
         },
         {binding, l(1, 0, 5),
           {var, l(1, 0, 1), "y"},
           {int, l(1, 4, 1), 3}
         }],
        {var, l(1, 9, 1), "y"}
      },
      ok_expr("let f() = x\ny = 3 in y")
    )
  % ensure no ambiguity with app
  , ?_assertEqual(
      {'let', l(0, 0, 1, 12),
        [{binding, l(4, 7),
           {var, l(4, 1), "f"},
           {fn, l(4, 7), [], {var, l(10, 1), "x"}}
         },
         {binding, l(1, 0, 7),
           {var, l(1, 0, 3), "y"},
           {int, l(1, 6, 1), 3}
         }],
        {var, l(1, 11, 1), "y"}
      },
      ok_expr("let f() = x\n(y) = 3 in y")
    )


  , ?_assertEqual(
      {if_let, l(0, 24),
        {'_', l(7, 1)},
        {atom, l(11, 3), hi},
        {atom, l(20, 4), foo},
        {unit, l(20, 4)}
      },
      ok_expr("if let _ = @hi then @foo")
    )
  , ?_assertEqual(
      {if_let, l(0, 37),
        {list, l(7, 2), []},
        {bool, l(12, 4), true},
        {str, l(22, 4), <<"hi">>},
        {str, l(32, 5), <<"hey">>}
      },
      ok_expr("if let [] = true then \"hi\" else \"hey\"")
    )
  , ?_assertEqual(
      {'let', l(0, 39),
        [{binding, l(4, 30),
           {var, l(4, 1), "x"},
           {if_let, l(8, 26),
             {int, l(15, 1), 1},
             {int, l(19, 1), 1},
             {int, l(26, 1), 1},
             {int, l(33, 1), 2}
           }
         }],
        {var, l(38, 1), "x"}
      },
      ok_expr("let x = if let 1 = 1 then 1 else 2 in x")
    )


  , ?_assertEqual(
      {match, l(0, 28), {int, l(6, 1), 1}, [
        {'case', l(10, 6), {int, l(10, 1), 1}, {var, l(15, 1), "x"}},
        {'case', l(18, 8), {float, l(18, 3), 5.7}, {var, l(25, 1), "y"}}
      ]},
      ok_expr("match 1 { 1 => x, 5.7 => y }")
    )
  , ?_assertEqual(
      {match, l(0, 0, 1, 10), {int, l(6, 1), 1}, [
        {'case', l(10, 6), {int, l(10, 1), 1}, {var, l(15, 1), "x"}},
        {'case', l(1, 0, 8), {float, l(1, 0, 3), 5.7}, {var, l(1, 7, 1), "y"}}
      ]},
      ok_expr("match 1 { 1 => x\n5.7 => y }")
    )
  % ensure no ambiguity with app
  , ?_assertEqual(
      {match, l(0, 0, 1, 12), {int, l(6, 1), 1}, [
        {'case', l(10, 6), {int, l(10, 1), 1}, {var, l(15, 1), "x"}},
        {'case', l(1, 0, 10), {float, l(1, 0, 5), 5.7}, {var, l(1, 9, 1), "y"}}
      ]},
      ok_expr("match 1 { 1 => x\n(5.7) => y }")
    )
  , ?_assertEqual(
      {match, l(0, 29), {bool, l(6, 4), true}, [
        {'case', l(13, 14), {bool, l(13, 5), false}, {bool, l(22, 5), false}}
      ]},
      ok_expr("match true { false => false }")
    )
  , ?_assertEqual(
      {match, l(0, 25), {char, l(6, 3), $a}, [
        {'case', l(12, 11), {char, l(12, 4), $\b}, {char, l(20, 3), $c}}
      ]},
      ok_expr("match 'a' { '\\b' => 'c' }")
    )
  , ?_assertEqual(
      {match, l(0, 26), {str, l(6, 4), <<"hi">>}, [
        {'case', l(13, 11),
          {str, l(13, 5), <<"hey">>},
          {str, l(22, 2), <<"">>}
        }
      ]},
      ok_expr("match \"hi\" { \"hey\" => \"\" }")
    )
  , ?_assertEqual(
      {match, l(0, 25), {atom, l(6, 3), hi}, [
        {'case', l(12, 11), {atom, l(12, 4), hey}, {atom, l(20, 3), ''}}
      ]},
      ok_expr("match @hi { @hey => @\"\" }")
    )
  , ?_assertEqual(
      {match, l(0, 18), {var, l(6, 1), "x"}, [
        {'case', l(10, 6), {var, l(10, 1), "y"}, {var, l(15, 1), "z"}}
      ]},
      ok_expr("match x { y => z }")
    )
  , ?_assertEqual(
      {match, l(0, 19), {var, l(6, 1), "x"}, [
        {'case', l(10, 7), {var_value, l(10, 2), "y"}, {var, l(16, 1), "z"}}
      ]},
      ok_expr("match x { &y => z }")
    )
  , ?_assertEqual(
      {match, l(0, 19), {var, l(6, 1), "x"}, [
        {'case', l(10, 7), {'_', l(10, 1)}, {unit, l(15, 2)}}
      ]},
      ok_expr("match x { _ => () }")
    )
  , ?_assertEqual(
      {match, l(0, 24), {con_token, l(6, 3), "Bar"}, [
        {'case', l(12, 10),
          {con_token, l(12, 3), "Bar"},
          {con_token, l(19, 3), "Bar"}
        }
      ]},
      ok_expr("match Bar { Bar => Bar }")
    )


  % Ensure ambiguity is resolved. The first three tests below ensure that the
  % second pair of brackets are considered the match cases. The fourth test
  % ensures that we don't incorrectly parse '_' as an expression, which we might
  % do to check if the braces represent a record update.
  , ?_assertEqual(
      {match, l(0, 34),
        {record, l(6, 13), {con_token, l(6, 3), "Bar"}, [
          {init, l(12, 5), {var, l(12, 1), "a"}, {int, l(16, 1), 3}}
        ]}, [
          {'case', l(22, 10),
            {con_token, l(22, 3), "Bar"},
            {con_token, l(29, 3), "Bar"}
          }
        ]
      },
      ok_expr("match Bar { a = 3 } { Bar => Bar }")
    )
  , ?_assertEqual(
      {match, l(0, 37),
        {record, l(6, 16), {con_token, l(6, 3), "Bar"}, [
          {init, l(12, 8), {var, l(12, 1), "f"},
            {fn, l(12, 8), [{var, l(14, 1), "x"}], {var, l(19, 1), "x"}}
          }
        ]}, [
          {'case', l(25, 10),
            {con_token, l(25, 3), "Bar"},
            {con_token, l(32, 3), "Bar"}
          }
        ]
      },
      ok_expr("match Bar { f(x) = x } { Bar => Bar }")
    )
  , ?_assertEqual(
      {match, l(0, 38),
        {record_ext, l(6, 17),
          {con_token, l(6, 3), "Bar"},
          {var, l(12, 1), "a"},
          [{init, l(16, 5), {var, l(16, 1), "b"}, {int, l(20, 1), 3}}]
        }, [
          {'case', l(26, 10),
            {con_token, l(26, 3), "Bar"},
            {con_token, l(33, 3), "Bar"}
          }
        ]
      },
      ok_expr("match Bar { a | b = 3 } { Bar => Bar }")
    )
  , ?_assertEqual(
      {match, l(0, 22), {con_token, l(6, 3), "Bar"}, [
        {'case', l(12, 8), {'_', l(12, 1)}, {con_token, l(17, 3), "Bar"}}
      ]},
      ok_expr("match Bar { _ => Bar }")
    )


  , ?_assertEqual(
      {match, l(0, 41),
        {field, l(6, 7),
          {con_token, l(6, 3), "Foo"},
          {con_token, l(10, 3), "Bar"}
        }, [
          {'case', l(16, 23),
            {field, l(16, 10),
              {con_token, l(16, 6), "Module"},
              {con_token, l(23, 3), "Bar"}
            },
            {field, l(30, 9),
              {con_token, l(30, 5), "Other"},
              {con_token, l(36, 3), "Bar"}
            }
          }
        ]
      },
      ok_expr("match Foo.Bar { Module.Bar => Other.Bar }")
    )
  , ?_assertEqual(
      {match, l(0, 33),
        {app, l(6, 6),
          {con_token, l(6, 3), "Bar"},
          [{int, l(10, 1), 9}]
        }, [
          {'case', l(15, 16),
            {app, l(15, 6),
              {con_token, l(15, 3), "Bar"},
              [{var, l(19, 1), "x"}]
            },
            {app, l(25, 6),
              {con_token, l(25, 3), "Bar"},
              [{int, l(29, 1), 3}]
            }
          }
        ]
      },
      ok_expr("match Bar(9) { Bar(x) => Bar(3) }")
    )
  , ?_assertEqual(
      {match, l(0, 50),
        {app, l(6, 10),
          {field, l(6, 7),
            {con_token, l(6, 3), "Foo"},
            {con_token, l(10, 3), "Bar"}
          },
          [{int, l(14, 1), 9}]
        }, [
          {'case', l(19, 29),
            {app, l(19, 13),
              {field, l(19, 10),
                {con_token, l(19, 6), "Module"},
                {con_token, l(26, 3), "Bar"}
              },
              [{var, l(30, 1), "x"}]
            },
            {app, l(36, 12),
              {field, l(36, 9),
                {con_token, l(36, 5), "Other"},
                {con_token, l(42, 3), "Bar"}
              },
              [{int, l(46, 1), 3}]
            }
          }
        ]
      },
      ok_expr("match Foo.Bar(9) { Module.Bar(x) => Other.Bar(3) }")
    )
  , ?_assertEqual(
      {match, l(0, 21), {list, l(6, 2), []}, [
        {'case', l(11, 8), {list, l(11, 2), []}, {list, l(17, 2), []}}
      ]},
      ok_expr("match [] { [] => [] }")
    )
  , ?_assertEqual(
      {match, l(0, 24), {list, l(6, 3), [{int, l(7, 1), 1}]}, [
        {'case', l(12, 10),
          {list, l(12, 3), [{var, l(13, 1), "x"}]},
          {list, l(19, 3), [{var, l(20, 1), "x"}]}
        }
      ]},
      ok_expr("match [1] { [x] => [x] }")
    )
  , ?_assertEqual(
      {match, l(0, 27), {list, l(6, 3), [{int, l(7, 1), 1}]}, [
        {'case', l(12, 13),
          {list, l(12, 6), [{var, l(13, 1), "x"}, {int, l(16, 1), 1}]},
          {list, l(22, 3), [{var, l(23, 1), "x"}]}
        }
      ]},
      ok_expr("match [1] { [x, 1] => [x] }")
    )
  , ?_assertEqual(
      {match, l(0, 26), {list, l(6, 3), [{int, l(7, 1), 1}]}, [
        {'case', l(12, 12),
          {cons, l(12, 7), [{'_', l(13, 1)}], {var, l(17, 1), "t"}},
          {var, l(23, 1), "t"}
        }
      ]},
      ok_expr("match [1] { [_ | t] => t }")
    )
  , ?_assertEqual(
      {match, l(0, 42),
        {tuple, l(6, 10), [
          {char, l(7, 3), $a},
          {atom, l(12, 3), hi}
        ]}, [
          {'case', l(19, 21),
            {char, l(19, 6), $\b},
            {tuple, l(29, 11), [{char, l(30, 3), $c}, {atom, l(35, 4), hey}]}
          }
        ]
      },
      ok_expr("match ('a', @hi) { ('\\b') => ('c', @hey) }")
    )
  , ?_assertEqual(
      {match, l(0, 45),
        {tuple, l(6, 10), [
          {char, l(7, 3), $a},
          {atom, l(12, 3), hi}
        ]}, [
          {'case', l(19, 24),
            {tuple, l(19, 9), [{char, l(20, 4), $\b}, {var, l(26, 1), "x"}]},
            {tuple, l(32, 11), [{char, l(33, 3), $c}, {atom, l(38, 4), hey}]}
          }
        ]
      },
      ok_expr("match ('a', @hi) { ('\\b', x) => ('c', @hey) }")
    )
  , ?_assertEqual(
      {binary_op, l(0, 22), '+',
        {match, l(0, 18), {int, l(6, 1), 1}, [
          {'case', l(10, 6), {'_', l(10, 1)}, {int, l(15, 1), 1}}
        ]},
        {int, l(21, 1), 2}
      },
      ok_expr("match 1 { _ => 1 } + 2")
    )


  , ?_assertEqual(
      {block, l(0, 11), [{str, l(2, 7), <<"hello">>}]},
      ok_expr("{ \"hello\" }")
    )
  , ?_assertEqual(
      {block, l(0, 30), [
        {atom, l(2, 4), foo},
        {map, l(8, 13), [{{str, l(9, 4), <<"hi">>}, {var, l(17, 3), "var"}}]},
        {bool, l(23, 5), false}
      ]},
      ok_expr("{ @foo; {\"hi\" => var}; false }")
    )
  ].

def_test_() ->
  [ ?_assertEqual(
      {global, l(0, 11),
        {var, l(0, 1), "f"},
        {fn, l(0, 11), [],
          {binary_op, l(6, 5), '+',
            {int, l(6, 1), 3},
            {int, l(10, 1), 5}
          }
        },
        false
      },
      ok_def("f() = 3 + 5")
    )
  , ?_assertEqual(
      {global, l(0, 12),
        {var, l(0, 1), "f"},
        {fn, l(0, 12), [{var, l(2, 1), "x"}],
          {binary_op, l(7, 5), '+',
            {var, l(7, 1), "x"},
            {int, l(11, 1), 5}
          }
        },
        false
      },
      ok_def("f(x) = x + 5")
    )
  , ?_assertEqual(
      {global, l(0, 15),
        {var, l(0, 1), "f"},
        {fn, l(0, 15), [{var, l(2, 1), "x"}, {var, l(5, 1), "y"}],
          {binary_op, l(10, 5), '+',
            {var, l(10, 1), "x"},
            {var, l(14, 1), "y"}
          }
        },
        false
      },
      ok_def("f(x, y) = x + y")
    )


  , ?_assertEqual(
      {global, l(0, 12), {var, l(7, 1), "a"}, {int, l(11, 1), 3}, true},
      ok_def("export a = 3")
    )
  , ?_assertEqual(
      {global, l(0, 18),
        {var, l(7, 1), "f"},
        {fn, l(7, 11), [],
          {binary_op, l(13, 5), '+',
            {int, l(13, 1), 3},
            {int, l(17, 1), 5}
          }
        },
        true
      },
      ok_def("export f() = 3 + 5")
    )


  , ?_assertEqual(
      {sig, l(0, 19),
        {var, l(0, 3), "foo"},
        {lam_te, l(6, 13),
          {con_token, l(6, 3), "Int"},
          {con_token, l(13, 6), "String"}
        }
      },
      ok_def("foo : Int -> String")
    )


  , ?_assertEqual(
      {enum, l(0, 0, 2, 1), {con_token, l(5, 7), "SumType"}, [
        {option, l(1, 2, 3), {con_token, l(1, 2, 3), "Foo"}, [], none},
        {option, l(1, 7, 16),
          {con_token, l(1, 7, 3), "Bar"},
          [{con_token, l(1, 11, 6), "String"}],
          {some, {atom, l(1, 19, 4), bar}}
        },
        {option, l(1, 25, 17),
          {con_token, l(1, 25, 3), "Baz"},
          [{con_token, l(1, 29, 3), "Int"},
           {gen_te, l(1, 34, 7),
             {con_token, l(1, 34, 7), "List"},
             [{con_token, l(1, 35, 5), "Float"}]
           }],
          none
        }
      ]},
      ok_def(
        "enum SumType {\n"
        "  Foo, Bar(String) @bar, Baz(Int, [Float])\n"
        "}"
      )
    )
  , ?_assertEqual(
      {enum, l(0, 0, 4, 1),
        {gen_te, l(5, 10), {con_token, l(5, 7), "SumType"}, [
          {tv_te, l(13, 1), "A", none}
        ]}, [
          {option, l(1, 2, 8),
            {con_token, l(1, 2, 3), "Foo"},
            [],
            {some, {atom, l(1, 6, 4), foo}}
          },
          {option, l(2, 2, 6),
            {con_token, l(2, 2, 3), "Bar"},
            [{tv_te, l(2, 6, 1), "A", none}],
            none
          },
          {option, l(3, 2, 17),
            {con_token, l(3, 2, 3), "Baz"},
            [{con_token, l(3, 6, 3), "Int"},
             {gen_te, l(3, 11, 7),
               {con_token, l(3, 11, 7), "List"},
               [{con_token, l(3, 12, 5), "Float"}]
             }],
            none
          }
        ]
      },
      ok_def(
        "enum SumType<A> {\n"
        "  Foo @foo\n"
        "  Bar(A)\n"
        "  Baz(Int, [Float])\n"
        "}"
      )
    )
  , ?_assertEqual(
      {enum, l(0, 0, 4, 1),
        {gen_te, l(5, 13), {con_token, l(5, 7), "SumType"}, [
          {tv_te, l(13, 1), "A", none},
          {tv_te, l(16, 1), "B", none}
        ]}, [
          {option, l(1, 2, 3),
            {con_token, l(1, 2, 3), "Foo"},
            [],
            none
          },
          {option, l(2, 2, 6),
            {con_token, l(2, 2, 3), "Bar"},
            [{tv_te, l(2, 6, 1), "A", none}],
            none
          },
          {option, l(3, 2, 18),
            {con_token, l(3, 2, 3), "Baz"},
            [{con_token, l(3, 6, 3), "Int"},
             {gen_te, l(3, 11, 3),
               {con_token, l(3, 11, 3), "List"},
               [{tv_te, l(3, 12, 1), "B", none}]
             }],
            {some, {atom, l(3, 16, 4), baz}}
          }
        ]
      },
      ok_def(
        "enum SumType<A, B> {\n"
        "  Foo\n"
        "  Bar(A)\n"
        "  Baz(Int, [B]) @baz\n"
        "}"
      )
    )


  , ?_assertEqual(
      {struct, l(0, 0, 2, 1), {con_token, l(7, 11), "ProductType"}, [
        {sig, l(1, 2, 12),
          {var, l(1, 2, 3), "foo"},
          {con_token, l(1, 8, 6), "String"}
        },
        {sig, l(1, 16, 17),
          {var, l(1, 16, 3), "bar"},
          {tuple_te, l(1, 22, 11), [
            {con_token, l(1, 23, 3), "Int"},
            {con_token, l(1, 28, 4), "Bool"}
          ]}
        }
      ]},
      ok_def(
        "struct ProductType {\n"
        "  foo : String, bar : (Int, Bool)\n"
        "}"
      )
    )
  , ?_assertEqual(
      {struct, l(0, 0, 3, 1),
        {gen_te, l(7, 14), {con_token, l(7, 11), "ProductType"}, [
          {tv_te, l(19, 1), "A", none}
        ]}, [
          {sig, l(1, 2, 7),
            {var, l(1, 2, 3), "foo"},
            {tv_te, l(1, 8, 1), "A", none}
          },
          {sig, l(2, 2, 17),
            {var, l(2, 2, 3), "bar"},
            {tuple_te, l(2, 8, 11), [
              {con_token, l(2, 9, 3), "Int"},
              {con_token, l(2, 14, 4), "Bool"}
            ]}
          }
        ]
      },
      ok_def(
        "struct ProductType<A> {\n"
        "  foo : A\n"
        "  bar : (Int, Bool)\n"
        "}"
      )
    )
  , ?_assertEqual(
      {struct, l(0, 0, 3, 1),
        {gen_te, l(7, 17), {con_token, l(7, 11), "ProductType"}, [
          {tv_te, l(19, 1), "A", none},
          {tv_te, l(22, 1), "B", none}
        ]}, [
          {sig, l(1, 2, 7),
            {var, l(1, 2, 3), "foo"},
            {tv_te, l(1, 8, 1), "A", none}
          },
          {sig, l(2, 2, 14),
            {var, l(2, 2, 3), "bar"},
            {tuple_te, l(2, 8, 8), [
              {con_token, l(2, 9, 3), "Int"},
              {tv_te, l(2, 14, 1), "B", none}
            ]}
          }
        ]
      },
      ok_def(
        "struct ProductType<A, B> {\n"
        "  foo : A\n"
        "  bar : (Int, B)\n"
        "}"
      )
    )


  , ?_assertEqual(
      {interface, l(0, 0, 2, 1), {con_token, l(10, 5), "Iface"}, [
        {sig, l(1, 2, 12),
          {var, l(1, 2, 3), "foo"},
          {con_token, l(1, 8, 6), "String"}
        },
        {sig, l(1, 16, 14),
          {var, l(1, 16, 3), "bar"},
          {lam_te, l(1, 22, 8),
            {tv_te, l(1, 22, 1), "T", none},
            {con_token, l(1, 27, 3), "Int"}
          }
        }
      ]},
      ok_def(
        "interface Iface {\n"
        "  foo : String, bar : T -> Int\n"
        "}"
      )
    )
  , ?_assertEqual(
      {interface, l(0, 0, 3, 1), {con_token, l(10, 8), "Mappable"}, [
        {sig, l(1, 2, 23),
          {var, l(1, 2, 3), "add"},
          {lam_te, l(1, 8, 17),
            {tv_te, l(1, 8, 1), "A", none},
            {lam_te, l(1, 13, 12),
              {gen_te, l(1, 13, 4),
                {tv_te, l(1, 13, 4), "T", none},
                [{tv_te, l(1, 15, 1), "A", none}]
              },
              {gen_te, l(1, 21, 4),
                {tv_te, l(1, 21, 4), "T", none},
                [{tv_te, l(1, 23, 1), "A", none}]
              }
            }
          }
        },
        {sig, l(2, 2, 20),
          {var, l(2, 2, 6), "length"},
          {lam_te, l(2, 11, 11),
            {gen_te, l(2, 11, 4),
              {tv_te, l(2, 11, 4), "T", none},
              [{tv_te, l(2, 13, 1), "B", none}]
            },
            {con_token, l(2, 19, 3), "Int"}
          }
        }
      ]},
      ok_def(
        "interface Mappable {\n"
        "  add : A -> T<A> -> T<A>\n"
        "  length : T<B> -> Int\n"
        "}"
      )
    )


  , ?_assertEqual(
      {impl, l(0, 0, 2, 1),
        {con_token, l(5, 5), "ToStr"},
        {con_token, l(15, 4), "Bool"}, [
          {init, l(1, 2, 17),
            {var, l(1, 2, 4), "to_s"},
            {fn, l(1, 2,  17),
              [{var, l(1, 7, 4), "bool"}],
              {var, l(1, 15, 4), "bool"}
            }
          }
        ]
      },
      ok_def(
        "impl ToStr for Bool {\n"
        "  to_s(bool) = bool\n"
        "}"
      )
    )
  , ?_assertEqual(
      {impl, l(0, 0, 3, 1),
        {con_token, l(5, 7), "Foo.Bar"},
        {gen_te, l(17, 8), {con_token, l(17, 8), "List"},
          [{tv_te, l(18, 6), "A", {some, {con_token, l(21, 3), "Foo"}}}]
        }, [
          {init, l(1, 2, 11),
            {var, l(1, 2, 3), "foo"},
            {fn, l(1, 2, 11), [], {char, l(1, 10, 3), $c}}
          },
          {init, l(2, 2, 11),
            {var, l(2, 2, 5), "other"},
            {atom, l(2, 10, 3), hi}
          }
        ]
      },
      ok_def(
        "impl Foo.Bar for [A: Foo] {\n"
        "  foo() = 'c'\n"
        "  other = @hi\n"
        "}"
      )
    )
  ].

import_test_() ->
  [ ?_assertEqual(
      {module, l(-1, 0, 10), {con_token, l(-1, 7, 3), "Mod"},
        [{import, l(0, 12), {str, l(7, 5), <<"foo">>}, []}],
        [{global, l(1, 0, 6),
           {var, l(1, 0, 1), "a"},
           {unit, l(1, 4, 2)},
           false
         }]
      },
      ok_prg(
        "module Mod\n"
        "import \"foo\"\n"
        "a = ()"
      )
    )
  , ?_assertEqual(
      {module, l(-1, 0, 10), {con_token, l(-1, 7, 3), "Mod"}, [
          {import, l(0, 37), {str, l(7, 5), <<"foo">>}, [
            {var, l(14, 3), "foo"},
            {con_token, l(19, 3), "Bar"},
            {variants, l(24, 12), "Baz"}
          ]}
        ],
        [{global, l(1, 0, 6),
           {var, l(1, 0, 1), "a"},
           {unit, l(1, 4, 2)},
           false
         }]
      },
      ok_prg(
        "module Mod\n"
        "import \"foo\" (foo, Bar, variants Baz)\n"
        "a = ()"
      )
    )
  , ?_assertEqual(
      {module, l(-1, 0, 10), {con_token, l(-1, 7, 3), "Mod"}, [
          {import, l(0, 0, 4, 1), {str, l(7, 5), <<"foo">>}, [
            {var, l(1, 2, 3), "foo"},
            {con_token, l(2, 2, 3), "Bar"},
            {variants, l(3, 2, 12), "Baz"}
          ]}
        ],
        [{global, l(5, 0, 6),
           {var, l(5, 0, 1), "a"},
           {unit, l(5, 4, 2)},
           false
         }]
      },
      ok_prg(
        "module Mod\n"
        "import \"foo\" (\n"
        "  foo\n"
        "  Bar\n"
        "  variants Baz\n"
        ")\n"
        "a = ()"
      )
    )
  , ?_assertEqual(
      {module, l(-1, 0, 10), {con_token, l(-1, 7, 3), "Mod"}, [
          {import, l(0, 18), {str, l(7, 5), <<"foo">>},
            [{var, l(14, 3), "foo"}]},
          {import, l(1, 0, 16), {str, l(1, 7, 9), <<"bar/baz">>}, []}
        ],
        [{global, l(2, 0, 6),
           {var, l(2, 0, 1), "a"},
           {unit, l(2, 4, 2)},
           false
         }]
      },
      ok_prg(
        "module Mod\n"
        "import \"foo\" (foo)\n"
        "import \"bar/baz\"\n"
        "a = ()"
      )
    )
  ].
