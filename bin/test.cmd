@echo off
set BOOTSTRAP=1
escript bin\par -o ebin src\parser.par
set BOOTSTRAP=

call bin\precompile.cmd
escript bin\rebar3 eunit
