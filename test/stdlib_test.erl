-module(stdlib_test).

-include_lib("eunit/include/eunit.hrl").
-include("../src/common.hrl").

stdlib_test_() ->
  % We use a setup/instantiator here to prevent eunit's lookahead from running
  % test_stdlib_path (an expensive generator) multiple times.
  Setup = fun() -> filelib:wildcard("test/lib/**/*.par") end,
  {setup, Setup, fun test_stdlib_path/1}.

test_stdlib_path(Paths) ->
  {ok, Cwd} = file:get_cwd(),
  Dir = utils:temp_dir(),

  Imports = lists:map(fun(Path) ->
    ["import ", $", filename:join(Cwd, Path), $", $\n]
  end, Paths),
  Contents = ["module Mod\n", Imports, "\na = 1\n"],

  ParentPath = filename:join(Dir, "mod.par"),
  ok = file:write_file(ParentPath, Contents),

  Result = type_system:infer_file(ParentPath),
  {ok, Comps, C} = type_system_test:check_ok(Result, user),
  Compiled = code_gen:compile_comps(Comps, C),

  lists:map(fun({Mod, Binary}) ->
    utils:remove_mod(Mod),
    code:load_binary(Mod, "", Binary)
  end, Compiled),

  {ParentMod, _} = hd(Compiled),
  par_native:init(ParentMod),

  lists:map(fun(Path) ->
    Root = filename:rootname(filename:basename(Path)),
    ModuleParts = lists:map(fun([H | T]) ->
      [string:uppercase([H]) | T]
    end, string:split(Root, "_", all)),

    Module = lists:flatten(ModuleParts),
    Mod = list_to_atom(Module),
    ordsets:fold(fun(TestName, FoldTestSet) ->
      [{generator, Mod, list_to_atom(TestName)} | FoldTestSet]
    end, [], utils:test_names(Module, C#ctx.g_env))
  end, Paths).
