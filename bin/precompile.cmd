@echo off
rem Must compile first to generate _build dir, used to compute libs below.
escript bin\rebar3 compile

set libs=
setlocal enabledelayedexpansion
for /d %%d in (_build\default\lib\*) do set libs=!libs! -pa %%d\ebin
setlocal disabledelayedexpansion

erl +B %libs% -noshell -eval "par:entry(code_gen, compile_stdlib, [])"
