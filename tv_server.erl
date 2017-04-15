-module(tv_server).
-behavior(gen_server).
-export([
  start_link/0,
  fresh/1,
  init/1,
  handle_call/3,
  handle_cast/2,
  handle_info/2,
  terminate/2,
  code_change/3
]).

start_link() -> gen_server:start_link(?MODULE, 0, []).
fresh(Pid) -> gen_server:call(Pid, fresh).

init(Count) -> {ok, Count}.
handle_call(fresh, _, Count) -> {reply, {tv, gen_name(Count)}, Count + 1}.

handle_cast(Msg, Count) ->
  io:format("Unexpected message: ~p~n", [Msg]),
  {noreply, Count}.

handle_info(Msg, Count) ->
  io:format("Unexpected message: ~p~n", [Msg]),
  {noreply, Count}.

terminate(normal, Count) ->
  io:format("tv_server (~p) terminated.~n", Count),
  ok.

code_change(_, State, _) -> {ok, State}.

gen_name(Count) when Count < 26 -> [$A + Count];
gen_name(Count) -> [$A + (Count rem 26)|gen_name(Count - 26)].
