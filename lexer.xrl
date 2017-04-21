Definitions.

INT = [0-9]+
FLOAT = {INT}+\.{INT}+
BOOL = (true|false)
VAR = [a-zA-Z][a-zA-Z0-9_]*
STR = "(\\.|[^\\"])*"
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
\| : {token, {'|', TokenLine}}.
if : {token, {'if', TokenLine}}.
then : {token, {'then', TokenLine}}.
else : {token, {'else', TokenLine}}.
let : {token, {'let', TokenLine}}.
in : {token, {'in', TokenLine}}.
{INT} : {token, {int, TokenLine, list_to_integer(TokenChars)}}.
{FLOAT} : {token, {float, TokenLine, list_to_float(TokenChars)}}.
{BOOL} : {token, {bool, TokenLine, list_to_atom(TokenChars)}}.
{STR} : {token, {str, TokenLine, drop_quotes(TokenChars)}}.
{VAR} : {token, {var, TokenLine, TokenChars}}.
{WHITESPACE}+ : skip_token.

Erlang code.

drop_quotes(Str) ->
  lists:sublist(Str, 2, length(Str) - 2).
