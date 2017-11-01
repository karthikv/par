-module(stdlib_test).

-include_lib("eunit/include/eunit.hrl").
-include("../src/common.hrl").

stdlib_test_() ->
  Result = type_system:infer_file("test/lib/base_test.par"),
  {ok, Comps, C} = type_system_test:check_ok(Result, user),
  Compiled = code_gen:compile_comps(Comps, C),

  lists:map(fun({Mod, Binary}) ->
    utils:remove_mod(Mod),
    code:load_binary(Mod, "", Binary)
  end, Compiled),

  #comp{module=Module} = hd(Comps),
  {Mod, _} = hd(Compiled),
  Mod:'_@init'(ordsets:new()),

  ordsets:fold(fun(TestName, FoldTestSet) ->
    [{generator, Mod, list_to_atom(TestName)} | FoldTestSet]
  end, [], utils:test_names(Module, C#ctx.g_env)).
