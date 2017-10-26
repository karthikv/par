-module(bootstrap_test).
-include_lib("eunit/include/eunit.hrl").

check_infer(Path) ->
  case type_system:infer_file(Path) of
    {ok, _, _} -> ?assert(true);
    {errors, _, _}=Errors ->
      io:format("~s", [reporter:format(Errors)]),
      ?assert(false)
  end.

lexer_test() -> check_infer("src/lexer.par").
parser_test() -> check_infer("src/parser.par").
