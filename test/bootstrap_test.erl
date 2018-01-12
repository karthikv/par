-module(bootstrap_test).
-include("../src/common.hrl").
-include_lib("eunit/include/eunit.hrl").

bootstrap_test_() ->
  {setup, fun set_env/0, fun unset_env/1, [
    ?_test(check_infer("src/lexer.par")),
    ?_test(check_infer("src/parser.par"))
  ]}.

set_env() -> os:putenv(?BOOTSTRAP_ENV, "1").
unset_env(_) -> os:unsetenv(?BOOTSTRAP_ENV).

check_infer(Path) ->
  Result = type_system:infer_file(Path),
  type_system_test:check_ok(Result).
