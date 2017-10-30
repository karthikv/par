-module(bootstrap_test).
-include_lib("eunit/include/eunit.hrl").

check_infer(Path) ->
  Result = type_system:infer_file(Path),
  type_system_test:check_ok(Result).

lexer_test() -> check_infer("src/lexer.par").
parser_test() -> check_infer("src/parser.par").
