-module(par).
-export([main/1]).
-include("common.hrl").

% TODO:
% - [2-3 weeks] Typeclasses + generics w/o concrete types (HKTs)
%   - Recursive case of instantiation
%   - passing iface fn to native fn; e.g. @lists:map(to_int, l)?
%   - Optimize simple app case
%   - Handle more rewrite cases
%   - Ensure necessary TVs are solved in type system
%   - In code gen, rewrite var_ref that comes from Module.field
%   - sig instantiation
%   - impls across modules?
%   - Multiple interface unification. How to get errors w/ A: Num <=> B: Other?
%   - HKT unification and typeclasses
%   - Validation to prevent struct/enum TE from being a gen TV from HKT?
%   - Extending interfaces?
%   - Implementations for builtin typeclasses?
%   - Allow ifaces on struct/enum params?
%   - Port exec interface tests to type system tests
%   - Bootstrap, fix, and ensure everything still works
% - Rename -Var to -VarRep when necessary
% - Rename var to id and var_ref to var?
% - Bug with recursive functions and type signatures
%   e.g.
%     foo : C: Collection -> Int
%     foo(c) = if length(c) > 10 then length(c) else foo([])
% - Bug with referencing global variable in pattern
%   - Also use ^ instead of & for matching existing variable
% - Builtin typeclasses
%   - Proper type class for non-functions
%   - Make pattern matching with var_value use proper type class
%   - Ord type class for comparison and sorting
% - Dot instead of ':' for native functions?
% - Put solver record into CG to avoid duplication of fields like nested_ivs?
% - [2 days] Exceptions
% - [2 days] Better pattern matching
%   - Negative numbers and unit in patterns
%   - Record types
%   - '=' sign
%   - Disallow pattern matching w/ struct Con(...) fn?
%   - Allow when clause and or?
% - [1 day] TV vs. Con parsing
% - [2 weeks] Stdlib
%   - Map/Set operations?
%   - Ref type?
%   - Character type for typeclasses
% - [1 week] REPL
%   - See if interpreter is even necessary
%   - Finish implementation of import, interfaces, records
%   - Interpreter better error messages and backtraces
% - [3 days] Second pass for error messages (see TODOs in code)
%   - Specify expected type for operators
%   - Only show rigid if it matters
%   - Hone in on specific record field like we hone in on args?
%   - Context surrounding add_err cases rather than just two types
%     - Error message with context when there's no else clause
%   - Norm types for error messages
%   - Detect basic infinite loop conditions
%   - Helpful message if main() not exported
%   - Struct/Enum name conflict w/ global causes hard-to-understand errors
%   - Alias from utils:qualify because of struct/enum name conflict?
%   - Import errors: import from same file twice, import self
%   - More descriptive error when there's a dup import from variant
%   - Show both locations for redef + other relevant errors
%   - "Expected closing '}'" messages might have wrong start location b/c
%     we use the keyword location!
%   - Better message for no impl of interface
%   - Better message for no impl of anon record type when there's a concrete
%     record type impl that matches
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
%
% Uncertain
% - Allow T only on rhs of iface type sig?
% - Operator |< to prepend an argument?
% - Force all block expressions except last to be type ()?
% - List indexing?

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
        {ok, C, Comps} ->
          {Time, Compiled} = timer:tc(code_gen, compile_comps, [Comps, C]),
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
