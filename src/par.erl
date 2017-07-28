-module(par).
-export([main/1]).
-include("errors.hrl").

% TODO:
% - [1 day] Direct imports
% - [3 days] Better syntax
%   - Can we do string concat on multiple lines?
%   - Enforce else clause to avoid ambiguity/confusion?
%   - Colon instead of @ for atoms?
% - [2-3 weeks] Typeclasses + generics w/o concrete types (HKTs)
%   - Allow ifaces on struct/enum params?
% - [2 days] Exceptions
% - [2 days] Better pattern matching
%   - Negative numbers and unit in patterns
%   - Record types
%   - Disallow pattern matching w/ struct Con(...) fn?
%   - Allow when clause and or?
% - [2 weeks] Stdlib
%   - Map/Set operations?
% - [1 week] REPL
%   - Interpreter import implementation
%   - Interpreter better error messages and backtraces
% - [3 days] Second pass for error messages (see TODOs in code)
%   - Specify expected type for operators
%   - Only show rigid if it matters
%   - Hone in on specific record field like we hone in on args?
%   - Context surrounding add_err cases rather than just two types
%   - Norm types for error messages
%   - Detect basic infinite loop conditions
%   - Helpful message if main() not exported
% - [1 week] Lexer/Parser error messages
%   - For "expected closing ___", mark matching open ___
%   - Maybe change enclosed methods to accept open tag as well?
%     - Would allow for more uniform error messages
%   - Test these errors
% - [2 weeks] Editor tooling for vim, atom, emacs, sublime
%   - Fix syntax highlighting for comments in enum for vim
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
%
% Uncertain
% - Operator |< to prepend an argument?
% - Force all block expressions except last to be type ()?
% - List indexing?
% - Type aliases?

main(Args) ->
  {ok, Dir} = file:get_cwd(),
  OptSpecs = [
    {out_dir, $o, "output directory", {string, Dir},
     "Directory to output compiled .beam file(s)."},
    {source_file, undefined, undefined, string,
     "Path to source file"}
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
      Path = case lists:keyfind(source_file, 1, Opts) of
        false ->
          ?ERR("Error: need one <source_file> argument~n"),
          getopt:usage(OptSpecs, "par"),
          halt(1);

        {source_file, Path_} -> utils:absolute(Path_)
      end,

      case type_system:infer_file(Path) of
        {ok, _, Comps} ->
          {Time, Compiled} = timer:tc(code_gen, compile_comps, [Comps]),
          {out_dir, OutDir} = lists:keyfind(out_dir, 1, Opts),

          lists:foreach(fun({Mod, Binary}) ->
            Filename = lists:concat([Mod, ".beam"]),
            file:write_file(filename:join(OutDir, Filename), Binary),
            io:format(standard_error, "~s~n", [Filename])
          end, Compiled),

          io:format(standard_error, "~pms~n", [Time div 1000]);

        Errors ->
          ?ERR("~s", [reporter:format(Errors)]),
          halt(1)
      end
  end.
