-module(par).
-export([main/1]).
-include("common.hrl").

% TODO:
% - [2 weeks] Stdlib
%   - Map/Set operations?
%   - Ensure stdlib functions in lexer/parser are all eliminated
% - Fork eunite and fix macro display
% - Catch keyword for try?
% - Change from unit to {con, "()"} for consistency?
% - Bug with referencing global variable in pattern
%   - Also use ^ instead of & for matching existing variable
% - Bug with global manager init ordering
% - Bad error message in enclosed_paren/brace when enclosed expression doesn't
%   finish. Error is "expected ... before end-of-file" even though it's not
%   the end of file
% - Assume Num is a closed typeclass so we can omit sig in to_float(3 : Int)
% - Think about bug with passing curried function to native
% - Syntax: List, Set, Map, Record
%   - New: [a, b], #[a, b], #{a => b, c => d}, {a = b, c = d}
%   - Put: [a, b | c], #[a, b | c], #{a => b, c => d | m}, {a = b, c = d | r}
% - Finalize questions surrounding syntax:
%   - Lowercase for TVs? If not, how to prevent confusion w/ Con?
%   - Record update syntax? Consistency w/ other data structures?
%   - Use | to separate cases for match/try?
%   - Use -> instead of => for match/try?
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
%   - "Expected closing '}'" messages might have wrong start location b/c
%     we use the keyword location!
%   - Better message for no impl of interface
%   - Better message for no impl of anon record type when there's a struct
%     type that matches
%   - Better message for T<A> <=> anon record or anon record ext
%   - Fix other_errors_test that ensures sig cst is unified first
%   - Better messages for indirect errors from T<B> due to T<A> being unified
%   - Add explicit error when assert let w/ a pattern that'll always match
%   - Impl error due to iface type sig, where type sig can be in another module
%   - Explanation for how to circumvent builtin redef error?
%   - For rigid errors, use same TVs as are in signatures
% - Website + Documentation
%
% Defer
% - Using EUnit from par
% - if-let condition and other condition (or maybe when statement?)
% - Hex escaped characters \xff or \x{...} in strings
% - Update naming conventions
% - Concurrency
% - Move gm_start into on_load?
% - Use NOTP for faster load time?
% - [1 week] Exhaustive pattern matching errors
% - [1 day] Test more parser error messages
% - [2 weeks] Editor tooling for vim, atom, emacs, sublime
%   - Fix syntax highlighting for comments in enum for vim
% - Type aliases
% - Use tuple for struct representation rather than map
% - Optimize simple app case for interfaces to not rewrite
% - Prevent passing iface fn to native fn; e.g. @lists:map(to_int, l)?
% - Rename ifaces to is unless referring to actual {interface, ...}
% - Rename -Var to -VarRep when necessary
% - Rename var to id and var_ref to var?
% - Put solver record into CG to avoid duplication of fields like nested_ivs?
% - Implementations for builtin typeclasses?
%   - Should we also exclude concatable, separable, etc. from sets?
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
%
% Uncertain
% - Allow T only on rhs of iface type sig?
% - Operator |< to prepend an argument?
% - Force all block expressions except last to be type ()?
%   - Enforce discarding?

main(Args) ->
  {ok, Dir} = file:get_cwd(),
  OptSpecs = [
    {out_dir, $o, "output directory", {string, Dir},
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

          Filenames = lists:map(fun({Mod, Binary}) ->
            Filename = lists:concat([Mod, ".beam"]),
            file:write_file(filename:join(OutDir, Filename), Binary),
            Filename
          end, Compiled),

          case proplists:get_value(test, Opts, false) of
            true ->
              #comp{module=Module} = hd(Comps),
              {Mod, _} = hd(Compiled),

              TestSet = ordsets:fold(fun(TestName, FoldTestSet) ->
                [{generator, Mod, list_to_atom(TestName)} | FoldTestSet]
              end, [], utils:test_names(Module, C#ctx.g_env)),

              code:add_patha(OutDir),
              par_native:init(Mod),
              eunit:test(TestSet, [no_tty, {report, {unite_compact, []}}]),
              eunit:stop();

            false ->
              io:format(standard_error, "~s~n", [string:join(Filenames, "\n")])
          end;

        Errors ->
          ?ERR("~s", [reporter:format(Errors)]),
          halt(1)
      end
  end.
