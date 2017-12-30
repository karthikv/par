-module(par).
-export([main/1]).
-include("common.hrl").

% TODO:
% - [2 weeks] Stdlib
%   - Description for exceptions??
%   - String.search: return empty array when re = ""?
% - Move Concat/Separate into stdlib. Rename union/subtract to concat/sep?
%   - Fix bug in separate for sets
%   - Add concat_all function
% - Don't infer redefinitions (think about dup gnrs, inconsistent metadata)
% - Bug with referencing global variable in pattern
%   - Also use ^ instead of & for matching existing variable
%   - ^Mod.foo in pattern; update docs
% - Precompile stdlib modules
% - Website + Documentation
%   - Commands to run each program in tutorial and output
%   - Ensure all code samples in tutorial work
%     - Update descriptions of |> and ^foo
%   - Copyright and icons8 link
%   - Keep mention of test framework on home page?
%   - Docs for stdlib
%     - Capture tests?
%     - Examples for `re` test
%     - Module prefixes in tests
%     - Section for implementations
%     - How to import modules
%   - Download page
%   - Make GitHub repo public, add GitHub link
%
% - Default args?
% - Confusion between Con and TV
% - Fork eunite and fix macro display
% - Parallelize code gen
% - Make warnings print to stderr?
% - Bad "Fat arrow or equals error" when writing { Class = "hi" }
% - Bad error when using map on Map<Attr, String> in docs.par
% - Native function w/o arity on rhs of |>
% - If # of args in sig is diff from decl, ignore sig
% - Better messages for indirect errors from T<B> due to T<A> being unified
%
% Defer
% - if-let condition and other condition (or maybe when statement?)
% - Hex escaped characters \xff or \x{...} in strings
% - Update naming conventions
% - Concurrency
% - Use NOTP for faster load time?
% - [1 week] Exhaustive pattern matching errors
% - [1 day] Test more parser error messages
% - [2 weeks] Editor tooling for vim, atom, emacs, sublime
%   - Fix syntax highlighting for comments in enum for vim
% - Type aliases
% - Use tuple for struct representation rather than map?
% - Prevent passing iface fn to native fn; e.g. @lists:map(to_int, l)?
% - Rename ifaces to Is unless referring to actual {interface, ...}
% - Rename -Var to -VarRep when necessary
% - Rename var to id and var_ref to var?
% - Implementations for builtin typeclasses?
%   - Should we also exclude concat, separate, etc. from sets?
% - Collection extends Sized?
% - [2 days] Better pattern matching
%   - Record/Struct types
%   - Map types
%   - '=' sign
%   - Allow when clause and or?
% - Eq/Proper typeclass for non-functions?
%   - Make pattern matching with var_value use proper type class
% - Accessing tag of enum?
% - Dot operator for composition?
% - _atom field for a module
% - Enforce newline between defs?
% - _ in expressions with operators
% - [1 week] REPL
%   - See if interpreter is even necessary
%   - Finish implementation of import, interfaces, records
%   - Interpreter better error messages and backtraces
% - [3 days] Second pass for error messages (see TODOs in code)
%   - Specify expected type for operators
%   - Hone in on specific record field like we hone in on args?
%   - Context surrounding add_err cases rather than just two types
%     - Error message with context when there's no else clause
%   - Detect basic infinite loop conditions
%   - Helpful message if main() not exported
%   - Struct/Enum name conflict w/ global causes hard-to-understand errors
%   - Alias from utils:qualify because of struct/enum name conflict?
%   - Import errors: import from same file twice
%   - More descriptive error when there's a dup import from variant
%   - Show both locations for redef + other relevant errors
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
% - Operator |< to prepend an argument?
% - Force all block expressions except last to be type ()?
% - Global exception handler for better printing

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
    {out_dir, $o, "output directory", {string, DefaultOutDir},
      "Directory to output compiled .beam file(s)."
    },
    {test, $t, "run tests", boolean,
      "Run tests in source file"
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

      case type_system:infer_file(Path) of
        {ok, Comps, C} ->
          Compiled = code_gen:compile_comps(Comps, C),
          OutDir = proplists:get_value(out_dir, Opts),

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

          Filenames = lists:map(fun({Mod, Binary}) ->
            Filename = lists:concat([Mod, ".beam"]),
            BeamPath = filename:join(OutDir, Filename),
            case file:write_file(BeamPath, Binary) of
              ok -> ok;
              {error, BeamReason} ->
                ?ERR(
                  "Couldn't write ~s: ~s~n",
                  [BeamPath, file:format_error(BeamReason)]
                ),
                halt(1)
            end,
            Filename
          end, Compiled),

          #comp{module=Module} = hd(Comps),
          {Mod, _} = hd(Compiled),
          code:add_patha(OutDir),
          par_native:init(Mod),

          case proplists:get_value(test, Opts, false) of
            true ->
              TestSet = ordsets:fold(fun(TestName, FoldTestSet) ->
                [{generator, Mod, list_to_atom(TestName)} | FoldTestSet]
              end, [], utils:test_names(Module, C#ctx.g_env)),

              eunit:test(TestSet, [no_tty, {report, {unite_compact, []}}]),
              eunit:stop();

            false ->
              Exported = erlang:function_exported(Mod, main, 0),
              if
                Exported -> Mod:main();
                true ->
                  ?ERR(
                    "Built ~p modules. No main() in module ~s; exiting.~n",
                    [length(Filenames), Module]
                  )
              end
          end;

        Errors ->
          ?ERR("~s", [reporter:format(Errors)]),
          halt(1)
      end
  end.
