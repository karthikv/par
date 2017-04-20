Definitions.

INT = [0-9]+
BOOL = (true|false)
VAR = [a-zA-Z][a-zA-Z0-9_]*
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
\| : {token, {'|', TokenLine}}.
if : {token, {'if', TokenLine}}.
then : {token, {'then', TokenLine}}.
else : {token, {'else', TokenLine}}.
let : {token, {'let', TokenLine}}.
in : {token, {'in', TokenLine}}.
{INT} : {token, {int, TokenLine, list_to_integer(TokenChars)}}.
{BOOL} : {token, {bool, TokenLine, TokenChars}}.
{VAR} : {token, {var, TokenLine, TokenChars}}.
{WHITESPACE}+ : skip_token.

Erlang code.
