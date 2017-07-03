-module(par).
-export([main/1]).
-include("errors.hrl").

% TODO:
% - Columns + display code in error message reporting
% - Direct imports
% - Write parser in par
% - Lexer doesn't account for newlines in comments
% - Struct literal test when parser supports it
% - Test lexer errors
% - Typeclasses + generics w/o concrete types (HKTs)
% - Exceptions
% - Move gm start into on_load?
% - Better pattern matching
%   - Record types
%   - Function args with definite type
%   - Disallow pattern matching w/ struct Con(...) fn?
% - Exhaustive pattern matching errors
% - Stdlib
%   - Map/Set operations?
% - Ensure embedded mode?
% - REPL
%   - Interpreter import implementation
% - Concurrency
% - Second pass for error messages (see TODOs in code)
%   - Parsing issue for match Con { ... }
%   - List error messages should include full List type
%   - Norm types for error messages
%   - Detect basic infinite loop conditions
%   - Helpful message if main() not exported
% - Update naming conventions
%
% Defer
% - Newlines instead of commas to separate match conditions, let vars, etc?
%   - Allow trailing commas
%   - Can we do string concat on multiple lines?
% - Using EUnit from par
% - if-let condition and other condition (or maybe when statement?)
% - Hex escaped characters \xff or \x{...} in strings
%
% Uncertain
% - Interpreter backtraces?
% - Force all block expressions except last to be type ()?
% - List indexing?
% - Change fat arrow to regular arrow?
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
        {errors, Errs} -> type_system:report_errors(Errs);

        {ok, _, Comps} ->
          {Time, Compiled} = timer:tc(code_gen, compile_comps, [Comps]),
          {out_dir, OutDir} = lists:keyfind(out_dir, 1, Opts),

          lists:foreach(fun({Mod, Binary}) ->
            Filename = lists:concat([Mod, ".beam"]),
            file:write_file(filename:join(OutDir, Filename), Binary),
            io:format(standard_error, "~s~n", [Filename])
          end, Compiled),

          io:format(standard_error, "~pms~n", [Time div 1000])
      end
  end.
