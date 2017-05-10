-module(global_env_server).
-behavior(gen_server).
-export([
  reload/0,
  start_link/0,
  get/2,
  set/3,
  stop/1,
  init/1,
  handle_call/3,
  handle_cast/2,
  handle_info/2,
  terminate/2,
  code_change/3
]).

reload() ->
  code:purge(?MODULE),
  {ok, _} = compile:file(?MODULE),
  code:load_file(?MODULE).

start_link() -> gen_server:start_link(?MODULE, #{}, []).
get(Name, Pid) -> gen_server:call(Pid, {get, Name}).
set(Name, Value, Pid) -> gen_server:call(Pid, {set, Name, Value}).
stop(Pid) -> gen_server:stop(Pid).

init(Env) -> {ok, Env}.
handle_call({get, Name}, _, Env) -> {reply, maps:get(Name, Env), Env};
handle_call({set, Name, Value}, _, Env) ->
  NewEnv = Env#{Name => Value},
  {reply, NewEnv, NewEnv}.

handle_cast(Msg, Env) ->
  io:format("Unexpected message: ~p~n", [Msg]),
  {noreply, Env}.

handle_info(Msg, Env) ->
  io:format("Unexpected message: ~p~n", [Msg]),
  {noreply, Env}.

terminate(normal, _) -> ok.
code_change(_, State, _) -> {ok, State}.
