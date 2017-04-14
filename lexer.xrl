Definitions.

VAR = [a-zA-Z][a-zA-Z0-9_]*
INT = [0-9]+
BOOL = (true|false)
WHITESPACE = [\s\t\n\r]

Rules.

{VAR} : {token, {var, TokenLine, TokenChars}}.
{INT} : {token, {int, TokenLine, list_to_integer(TokenChars)}}.
{BOOL} : {token, {bool, TokenLine, TokenChars}}.
if : {token, {'if', TokenLine}}.
then : {token, {'then', TokenLine}}.
else : {token, {'else', TokenLine}}.
= : {token, {'=', TokenLine}}.
\( : {token, {'(', TokenLine}}.
\) : {token, {')', TokenLine}}.
, : {token, {',', TokenLine}}.
\+ : {token, {'+', TokenLine}}.
{WHITESPACE}+ : skip_token.

Erlang code.
