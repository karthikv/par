Definitions.

INT = [0-9]+
FLOAT = {INT}+\.{INT}+
BOOL = (true|false)
STR = "(\\.|[^\\"])*"
ATOM = @[a-zA-Z0-9_@]+
VAR = [a-z][a-zA-Z0-9_]*
TV = [A-Z]
CON = [A-Z][a-zA-Z0-9_]+
WHITESPACE = [\s\t\n\r]

Rules.

\= : {token, {'=', TokenLine}}.
\( : {token, {'(', TokenLine}}.
\) : {token, {')', TokenLine}}.
\, : {token, {',', TokenLine}}.
\=\= : {token, {'==', TokenLine}}.
\!\= : {token, {'!=', TokenLine}}.
\|\| : {token, {'||', TokenLine}}.
\&\& : {token, {'&&', TokenLine}}.
\! : {token, {'!', TokenLine}}.
\> : {token, {'>', TokenLine}}.
\< : {token, {'<', TokenLine}}.
\>\= : {token, {'>=', TokenLine}}.
\<\= : {token, {'<=', TokenLine}}.
\+ : {token, {'+', TokenLine}}.
\- : {token, {'-', TokenLine}}.
\* : {token, {'*', TokenLine}}.
\/ : {token, {'/', TokenLine}}.
\+\+ : {token, {'++', TokenLine}}.
\-\- : {token, {'--', TokenLine}}.
\| : {token, {'|', TokenLine}}.
\:\: : {token, {'::', TokenLine}}.
\: : {token, {':', TokenLine}}.
\-\> : {token, {'->', TokenLine}}.
\; : {token, {';', TokenLine}}.
discard : {token, {discard, TokenLine}}.
if : {token, {'if', TokenLine}}.
then : {token, {then, TokenLine}}.
else : {token, {else, TokenLine}}.
let : {token, {'let', TokenLine}}.
in : {token, {in, TokenLine}}.
{INT} : {token, {int, TokenLine, list_to_integer(TokenChars)}}.
{FLOAT} : {token, {float, TokenLine, list_to_float(TokenChars)}}.
{BOOL} : {token, {bool, TokenLine, list_to_atom(TokenChars)}}.
{STR} : {token, {str, TokenLine, list_to_binary(drop_quotes(TokenChars))}}.
\@{STR} : {token, {atom, TokenLine, list_to_atom(drop_quotes(tl(TokenChars)))}}.
{ATOM} : {token, {atom, TokenLine, list_to_atom(tl(TokenChars))}}.
{VAR} : {token, {var, TokenLine, TokenChars}}.
\[ : {token, {'[', TokenLine}}.
\] : {token, {']', TokenLine}}.
\{ : {token, {'{', TokenLine}}.
\} : {token, {'}', TokenLine}}.
\=\> : {token, {'=>', TokenLine}}.
\# : {token, {'#', TokenLine}}.
{TV} : {token, {sig_tv, TokenLine, TokenChars}}.
{CON} : {token, {sig_con, TokenLine, TokenChars}}.
{WHITESPACE}+ : skip_token.

Erlang code.

drop_quotes(Str) ->
  lists:sublist(Str, 2, length(Str) - 2).
