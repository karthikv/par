-module(bootstrap_test).
-include_lib("eunit/include/eunit.hrl").

lexer_test() -> {ok, _, _} = type_system:infer_file("src/lexer.par").
parser_test() -> {ok, _, _} = type_system:infer_file("src/parser.par").
