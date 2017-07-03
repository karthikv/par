-module(tv_server).
-behavior(gen_server).
-export([
  start_link/0,
  next_name/1,
  next_gnr_id/1,
  fresh/1,
  fresh_gnr_id/1,
  fresh/2,
  stop/1,
  init/1,
  handle_call/3,
  handle_cast/2,
  handle_info/2,
  terminate/2,
  code_change/3
]).

start_link() -> gen_server:start_link(?MODULE, {0, 0}, []).
next_name(Pid) -> gen_server:call(Pid, next_name).
next_gnr_id(Pid) -> gen_server:call(Pid, next_gnr_id).
fresh(Pid) -> {tv, next_name(Pid), none, false}.
fresh_gnr_id(Pid) -> {{tv, next_name(Pid), none, false}, next_gnr_id(Pid)}.
fresh(I, Pid) -> {tv, next_name(Pid), I, false}.
stop(Pid) -> gen_server:stop(Pid).

init({Count, NextID}) -> {ok, {Count, NextID}}.
handle_call(next_name, _, {Count, NextID}) ->
  {reply, [$* | lists:reverse(gen_name(Count))], {Count + 1, NextID}};
handle_call(next_gnr_id, _, {Count, NextID}) ->
  {reply, NextID, {Count, NextID + 1}}.

handle_cast(Msg, State) ->
  io:format("Unexpected message: ~p~n", [Msg]),
  {noreply, State}.

handle_info(Msg, State) ->
  io:format("Unexpected message: ~p~n", [Msg]),
  {noreply, State}.

terminate(normal, _) -> ok.
code_change(_, State, _) -> {ok, State}.

gen_name(Count) ->
  case trunc(Count / 26) of
    0 -> [$A + Count];
    Next -> [$A + Count rem 26 | gen_name(Next)]
  end.