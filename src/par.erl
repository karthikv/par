-module(par).
-export([entry/0, entry/3, main/1]).
-include("common.hrl").

% TODO:
% - Don't infer redefinitions (think about dup gnrs, inconsistent metadata)
% - Docs capture tests?
%   - Add else clause to try/catch
% - Error message "Missing a pattern of the form None()" - remove parens
%
% - Default args?
% - Confusion between Con and TV
% - Fork eunite and fix macro display
% - Parallelize code gen, don't reset counter state each time
% - Make warnings print to stderr?
% - Bad "Fat arrow or equals error" when writing { Class = "hi" }
% - Allow native function w/o arity on rhs of |>
% - If # of args in sig is diff from decl, ignore sig
% - Better messages for indirect errors from T<B> due to T<A> being unified
% - Improve io:put_char badarg errors when file isn't opened with right mode
% - Description for exceptions?
% - In docs, link to types from within signatures?
% - Suggestions for what to import
% - Edit distance for typos
% - Hone in on specific record fields for error messages
% - Add when support to match statement
% - Global exception handler for better printing
% - Remove "then" keyword?
%
% - Hex escaped characters \xff or \x{...} in strings
% - Working with multiple Erlang processes
% - [2 weeks] Editor tooling for vim, atom, emacs, sublime
%   - Fix syntax highlighting for comments in enum for vim
% - Type aliases
% - Prevent passing iface fn to native fn; e.g. @lists:map(to_int, l)?
% - Rename ifaces to Is unless referring to actual {interface, ...}
% - Rename -Var to -VarRep when necessary
% - Rename var to id and var_ref to var?
% - Implementations for ord typeclass?
% - Collection extends Sized?
% - [2 days] Better pattern matching
%   - Record/Struct types
%   - Map types
%   - '=' sign
%   - Allow when clause and or?
% - Accessing tag of enum?
% - _atom field for a module
% - Enforce newline between defs?
% - Allow _ in expressions with operators?
% - REPL
%   - See if interpreter is even necessary
%   - Finish implementation of import, interfaces, records
%   - Interpreter better error messages and backtraces
% - Second pass for error messages (see TODOs in code)
%   - Specify expected type for operators
%   - Context surrounding add_err cases rather than just two types
%     - Error message with context when there's no else clause
%   - Detect basic infinite loop conditions
%   - Struct/Enum name conflict w/ global causes hard-to-understand errors
%   - Alias from utils:qualify because of struct/enum name conflict?
%   - Import errors: import from same file twice
%   - Better message for no impl of interface
%   - Better message for no impl of anon record type when there's a struct
%     type that matches
%   - Better message for T<A> <=> anon record or anon record ext
%   - Fix other_errors_test that ensures sig cst is unified first
%   - Add explicit error when assert let w/ a pattern that'll always match
%   - Impl error due to iface type sig, where type sig can be in another module
%   - Explanation for how to circumvent builtin redef error?
%   - For rigid errors, use same TVs as are in signatures
%   - Keep con/iface qualified if ambiguous, or always qualify
% - Assume Num is a closed typeclass so we can omit sig in to_float(3 : Int)
% - Check and make comma/newline parsing consistent
% - Syntax: List, Set, Map, Record
%   - New: [a, b], #[a, b], {a => b, c => d}, {a = b, c = d}
%   - Put: [a, b | c], #[a, b | c], {a => b, c => d | m}, {a = b, c = d | r}
% - Operator |>> to append an argument?
% - Force all block expressions except last to be type ()?

entry() -> entry(?MODULE, main, [init:get_plain_arguments()]).

entry(Module, Fn, Args) ->
  try
    apply(Module, Fn, Args)
  catch
    Class:Reason ->
      Columns = case io:columns() of
        {ok, C} -> C;
        _ -> 80
      end,
      Raw = lib:format_exception(
        1,
        Class,
        Reason,
        erlang:get_stacktrace(),
        fun(_, _, _) -> false end,
        fun(T, I) -> io_lib_pretty:print(T, I, Columns, -1) end
      ),

      Formatted = case Class of
        throw ->
          case string:find(Raw, "\n") of
            nomatch -> Raw;
            After ->
              Pretty = par_native:to_pretty(Reason, Columns, 0),
              ["Exception: ", Pretty, After]
          end;

        _ -> Raw
      end,
      ?ERR("~s~n", [Formatted])
  end,

  halt(0).

main(Args) ->
  Release = erlang:system_info(otp_release),
  case string:to_integer(Release) of
    {OTP, []} when OTP >= 20 -> ok;
    _ ->
      ?ERR(
        "Par requires Erlang/OTP 20 or higher, but you have ~s~n",
        [Release]
      ),
      halt(1)
  end,

  {ok, Cwd} = file:get_cwd(),
  DefaultOutDir = filename:join([Cwd, "_build", "par"]),

  OptSpecs = [
    {out_dir, $o, "out-dir", {string, DefaultOutDir},
      "Directory to output compiled .beam file(s)."
    },
    {test, $t, "test", undefined,
      "Run tests in source file"
    },
    {stats, undefined, "stats", undefined,
      "Show statistics about how long compilation took."
    },
    {source_file, undefined, undefined, string,
      "Path to source file"
    }
  ],

  case getopt:parse(OptSpecs, Args) of
    {error, {Reason, Data}} ->
      ?ERR("Error: ~s (~p)~n", [Reason, Data]),
      getopt:usage(OptSpecs, "par"),
      halt(1);

    {ok, {_, Left}} when length(Left) > 0 ->
      ?ERR("Error: need only one <source_file> argument~n"),
      getopt:usage(OptSpecs, "par"),
      halt(1);

    {ok, {Opts, []}} ->
      Path = case proplists:get_value(source_file, Opts) of
        undefined ->
          ?ERR("Error: need one <source_file> argument~n"),
          getopt:usage(OptSpecs, "par"),
          halt(1);

        Path_ -> utils:absolute(Path_)
      end,

      run(Path, Opts)
  end.

run(Path, Opts) ->
  {InferTime, Inferred} = measure(type_system, infer_file, [Path]),
  case Inferred of
    {ok, Comps, C, _} ->
      Bootstrapping = ?BOOTSTRAPPING(),
      {GenTime, {Compiled, _}} = measure(
        code_gen,
        compile_comps,
        [Comps, C, Bootstrapping]
      ),
      OutDir = utils:absolute(proplists:get_value(out_dir, Opts)),

      % ensure_dir ensures the *parent* directory exists, so we need to
      % first join the OutDir with some arbitrary filename.
      case filelib:ensure_dir(filename:join(OutDir, "foo")) of
        ok -> ok;
        {error, OutReason} ->
          ?ERR(
            "Couldn't create output directory ~s: ~s~n",
            [OutDir, file:format_error(OutReason)]
          ),
          halt(1)
      end,

      StdlibStats = case Bootstrapping of
        true ->
          {LoadTime, AllCompiled} = measure(fun() ->
            lists:map(fun
              ({compiled, _, _}=E) -> E;
              ({precompiled, Mod, Existing}) ->
                {ok, Binary, _} = erl_prim_loader:get_file(Existing),
                {compiled, Mod, Binary}
            end, Compiled)
          end),

          {PrepTime, _} = measure(
            utils,
            prep_compiled,
            [AllCompiled, OutDir]
          ),
          ["Load stdlibs: ", LoadTime, "\nPrepare stdlibs: ", PrepTime, $\n];

        false ->
          lists:foreach(fun({compiled, Mod, Binary}) ->
            OutPath = filename:join(OutDir, atom_to_list(Mod) ++ ".beam"),
            ok = file:write_file(OutPath, Binary)
          end, Compiled),

          code:add_patha(OutDir),
          []
      end,

      case proplists:get_value(stats, Opts, false) of
        true ->
          Stats = [
            "Inference: ", InferTime, "\nCode generation: ", GenTime, $\n |
            StdlibStats
          ],
          ?ERR("~s", [Stats]);

        false -> ok
      end,

      #comp{module=Module} = hd(Comps),
      {compiled, Mod, _} = hd(Compiled),

      case proplists:get_value(test, Opts, false) of
        true ->
          TestSet = ordsets:fold(fun(TestName, FoldTestSet) ->
            [{generator, Mod, list_to_atom(TestName)} | FoldTestSet]
          end, [], utils:test_names(Module, C#ctx.g_env)),

          eunit:test(TestSet, [no_tty, {report, {unite_compact, []}}]),
          eunit:stop();

        false ->
          {module, Mod} = code:ensure_loaded(Mod),
          Exported = erlang:function_exported(Mod, main, 0),
          if
            Exported -> Mod:main();
            true ->
              BuiltMsg = case length(Compiled) of
                1 -> "Built 1 module.";
                Num -> io_lib:format("Built ~p modules.", [Num])
              end,
              ?ERR("~s No main() in module ~s; exiting.~n", [BuiltMsg, Module])
          end
      end;

    Errors ->
      ?ERR("~s", [reporter:format(Errors)]),
      halt(1)
  end.

measure(Mod, Fn, Args) ->
  {Time, Result} = timer:tc(Mod, Fn, Args),
  {format_time(Time), Result}.
measure(Fun) ->
  {Time, Result} = timer:tc(Fun),
  {format_time(Time), Result}.

format_time(Time) -> io_lib:format("~pms", [Time / 1000]).
