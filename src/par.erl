-module(par).
-export([main/1]).

-define(ERR(Str), io:format(standard_error, Str, [])).
-define(ERR(Str, Args), io:format(standard_error, Str, Args)).

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
      % TODO: exit code?
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

        {source_file, Path_} -> Path_
      end,
      {ok, Prg} = file:read_file(Path),

      case type_system:infer_prg(binary_to_list(Prg)) of
        {errors, Errs} -> type_system:report_errors(Errs);

        {ok, _, Ast} ->
          {Time, {Mod, Binary}} = timer:tc(code_gen, compile_ast, [Ast]),
          {out_dir, Dir} = lists:keyfind(out_dir, 1, Opts),
          Filename = lists:concat([Mod, '.beam']),

          file:write_file(filename:join([Dir, Filename]), Binary),
          io:format(standard_error, "~s ~pms~n", [Filename, Time div 1000])
      end
  end.
