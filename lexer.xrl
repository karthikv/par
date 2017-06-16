Definitions.

INT = [0-9]+
FLOAT = {INT}+\.{INT}+
BOOL = (true|false)
STR = "(\\.|[^\\"])*"
ATOM = @[a-zA-Z0-9_@]+
WORD = [a-zA-Z0-9_]
VAR = ([a-z]{WORD}*|_{WORD}+)
TV = [A-Z]
CON = [A-Z][a-zA-Z0-9_]+
WHITESPACE = [\s\t\n\r]
COMMENT = //.*

Rules.

\= : {token, {'=', TokenLine}}.
\( : {token, {'(', TokenLine}}.
\) : {token, {')', TokenLine}}.
\, : {token, {',', TokenLine}}.
\=\= : {token, {'==', TokenLine}}.
\!\= : {token, {'!=', TokenLine}}.
\|\| : {token, {'||', TokenLine}}.
\&\& : {token, {'&&', TokenLine}}.
\|\> : {token, {'|>', TokenLine}}.
\! : {token, {'!', TokenLine}}.
\> : {token, {'>', TokenLine}}.
\< : {token, {'<', TokenLine}}.
\>\= : {token, {'>=', TokenLine}}.
\<\= : {token, {'<=', TokenLine}}.
\+ : {token, {'+', TokenLine}}.
\- : {token, {'-', TokenLine}}.
\* : {token, {'*', TokenLine}}.
\/ : {token, {'/', TokenLine}}.
\% : {token, {'%', TokenLine}}.
\+\+ : {token, {'++', TokenLine}}.
\-\- : {token, {'--', TokenLine}}.
\. : {token, {'.', TokenLine}}.
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
match : {token, {match, TokenLine}}.
enum : {token, {enum_token, TokenLine}}.
struct : {token, {struct_token, TokenLine}}.
{INT} : {token, {int, TokenLine, list_to_integer(TokenChars)}}.
{FLOAT} : {token, {float, TokenLine, list_to_float(TokenChars)}}.
{BOOL} : {token, {bool, TokenLine, list_to_atom(TokenChars)}}.
{STR} : {token, {str, TokenLine, list_to_binary(drop_quotes(TokenChars))}}.
\@{STR} : {token, {atom, TokenLine, list_to_atom(drop_quotes(tl(TokenChars)))}}.
{ATOM} : {token, {atom, TokenLine, list_to_atom(tl(TokenChars))}}.
{VAR} : {token, {var, TokenLine, TokenChars}}.
\_ : {token, {'_', TokenLine}}.
\[ : {token, {'[', TokenLine}}.
\] : {token, {']', TokenLine}}.
\{ : {token, {'{', TokenLine}}.
\} : {token, {'}', TokenLine}}.
\=\> : {token, {'=>', TokenLine}}.
\# : {token, {'#', TokenLine}}.
{TV} : {token, {tv_token, TokenLine, TokenChars}}.
{CON} : {token, {con_token, TokenLine, list_to_atom(TokenChars)}}.
{WHITESPACE}+ : skip_token.
{COMMENT} : skip_token.

Erlang code.

drop_quotes(Str) ->
  lists:sublist(Str, 2, length(Str) - 2).
