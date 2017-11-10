-module(stdlib_test).

-include_lib("eunit/include/eunit.hrl").
-include("../src/common.hrl").

stdlib_test_() ->
  [test_stdlib_path(Path) ||
   Path <- filelib:wildcard("test/lib/**/*.par")].

test_stdlib_path(Path) ->
  Result = type_system:infer_file(Path),
  {ok, Comps, C} = type_system_test:check_ok(Result, user),
  Compiled = code_gen:compile_comps(Comps, C),

  lists:map(fun({Mod, Binary}) ->
    utils:remove_mod(Mod),
    code:load_binary(Mod, "", Binary)
  end, Compiled),

  #comp{module=Module} = hd(Comps),
  {Mod, _} = hd(Compiled),
  par_native:init(Mod),

  ordsets:fold(fun(TestName, FoldTestSet) ->
    [{generator, Mod, list_to_atom(TestName)} | FoldTestSet]
  end, [], utils:test_names(Module, C#ctx.g_env)).
