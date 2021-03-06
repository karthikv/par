-module(stdlib_test).

-include_lib("eunit/include/eunit.hrl").
-include("../src/common.hrl").

stdlib_test_() ->
  % If we don't use a setup/instantiator here, eunit's lookahead could make
  % us compile the stdlib multiple times, which is expensive.
  {setup, fun compile_stdlib/0, fun remove_stdlib/1, fun test_stdlib/1}.

compile_stdlib() ->
  Paths = filelib:wildcard("test/lib/**/*.par"),
  {ok, Cwd} = file:get_cwd(),
  Dir = utils:temp_dir(),

  Imports = lists:map(fun(Path) ->
    ["import ", $", filename:join(Cwd, Path), $", $\n]
  end, Paths),
  Contents = ["module Mod\n", Imports],

  ParentPath = filename:join(Dir, "mod.par"),
  ok = file:write_file(ParentPath, Contents),

  Result = type_system:infer_file(ParentPath),
  {ok, Comps, C, _} = type_system_test:check_ok(Result, user),

  {Compiled, _} = code_gen:compile_comps(Comps, C),
  utils:prep_compiled(Compiled, Dir),
  {Compiled, Dir, C}.

test_stdlib({Compiled, _, C}) ->
  Tests = lists:map(fun
    ({compiled, Mod, _}) ->
      Module = utils:unqualify(atom_to_list(Mod)),
      ordsets:fold(fun(TestName, FoldTestSet) ->
        [{generator, Mod, list_to_atom(TestName)} | FoldTestSet]
      end, [], utils:test_names(Module, C#ctx.g_env));

    ({precompiled, _, _}) -> []
  end, Compiled),

  {inparallel, 48, Tests}.

remove_stdlib({Compiled, Dir, _}) ->
  utils:remove_compiled(Compiled, Dir),
  ok.
