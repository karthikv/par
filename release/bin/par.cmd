@echo off

if "%PAR_ROOT%" == "" (
  set root=C:\par
) else (
  set root=%PAR_ROOT%
)

if not exist %root% (
  echo Par isn't installed at %root%. If you installed it to a different
  echo location, set the PAR_ROOT environment variable to that directory.
  exit /B 1
)

set libs=
setlocal enabledelayedexpansion
for /d %%d in (%root%\lib\*) do set libs=!libs! -pa %%d\ebin
setlocal disabledelayedexpansion

erl +B %libs% -noshell -s par entry -extra %*
