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
  {Paths, Compiled, C}.

test_stdlib({Paths, _, C}) ->
  Tests = lists:map(fun(Path) ->
    Root = filename:rootname(filename:basename(Path)),
    ModuleParts = lists:map(fun([H | T]) ->
      [string:uppercase([H]) | T]
    end, string:split(Root, "_", all)),

    Module = lists:flatten(ModuleParts),
    Mod = list_to_atom(Module),
    ordsets:fold(fun(TestName, FoldTestSet) ->
      [{generator, Mod, list_to_atom(TestName)} | FoldTestSet]
    end, [], utils:test_names(Module, C#ctx.g_env))
  end, Paths),

  {inparallel, 48, Tests}.

remove_stdlib({_, Compiled, _}) ->
  % Must explicitly remove all modules. Some of these modules are from *new*
  % stdlibs. We don't want the old parser/lexer to use new stdlibs.
  [utils:remove_mod(Mod) || {Mod, _} <- Compiled],
  ok.
