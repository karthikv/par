Nonterminals
  prg import_list def def_list
  global var_list expr expr_list
  kv_list start_record init_list mul neg lam
  let_list let_init start_match match_list semi_list
  pattern pattern_con pattern_list
  te te_con te_list enum option_list option
  struct field_list field tv_list.

Terminals
  '=' '(' ')' ','
  '==' '!=' '||' '&&' '|>' '!' '>' '<' '>=' '<='
  '+' '-' '*' '/' '%'
  '++' '--' '.' '|' '::' ':' '->' ';' '$'
  module import export enum_token struct_token
  if then else let in match discard
  int float bool char str atom var '_'
  '[' ']' '{' '}' '=>' '#'
  tv_token con_token.

Rootsymbol prg.

prg -> module con_token import_list def_list :
  {module, ?LOC('$1'), '$2', '$3', '$4'}.

import_list -> '$empty' : [].
import_list -> import str import_list :
  [{import, ?LOC('$1'), '$2'} | '$3'].

def -> global : '$1'.
def -> var '::' te : {sig, ?LOC('$1'), '$1', '$3'}.
def -> enum : '$1'.
def -> struct : '$1'.

def_list -> '$empty' : [].
def_list -> def def_list : ['$1' | '$2'].

global -> var '=' expr : {global, ?LOC('$1'), '$1', '$3', false}.
global -> var '(' ')' '=' expr :
  {global, ?LOC('$1'), '$1', {fn, ?LOC('$1'), [], '$5'}, false}.
global -> var '(' var_list ')' '=' expr :
  {global, ?LOC('$1'), '$1', {fn, ?LOC('$1'), '$3', '$6'}, false}.
global -> export global : setelement(5, '$2', true).

var_list -> var : ['$1'].
var_list -> var ',' var_list : ['$1' | '$3'].

expr -> '(' ')' : {none, ?LOC('$1')}.
expr -> int : '$1'.
expr -> float : '$1'.
expr -> bool : '$1'.
expr -> char : '$1'.
expr -> str : '$1'.
expr -> atom : '$1'.
expr -> var : '$1'.
expr -> '.' var : {field, ?LOC('$1'), '$2'}.
expr -> con_token : '$1'.
expr -> '[' ']' : {list, ?LOC('$1'), []}.
expr -> '[' expr_list ']' : {list, ?LOC('$1'), '$2'}.
expr -> '(' expr ',' expr_list ')' :
  {tuple, ?LOC('$1'), ['$2' | '$4']}.
expr -> '(' expr ')' : '$2'.
expr -> '{' '}' : {map, ?LOC('$1'), []}.
expr -> '{' kv_list '}' : {map, ?LOC('$1'), '$2'}.
expr -> '{' init_list '}' : {record, ?LOC('$1'), '$2'}.
expr -> '{' expr '|' init_list '}' :
  {update_record, ?LOC('$1'), '$2', '$4'}.
% TODO: allow con_token . con_token in updated parser
expr -> con_token start_record init_list '}' :
  {record, ?LOC('$1'), '$1', '$3'}.
expr -> expr '==' expr : {first('$2'), ?LOC('$1'), '$1', '$3'}.
expr -> expr '!=' expr : {first('$2'), ?LOC('$1'), '$1', '$3'}.
expr -> expr '||' expr : {first('$2'), ?LOC('$1'), '$1', '$3'}.
expr -> expr '&&' expr : {first('$2'), ?LOC('$1'), '$1', '$3'}.
expr -> expr '|>' expr : {first('$2'), ?LOC('$1'), '$1', '$3'}.
expr -> expr '>' expr : {first('$2'), ?LOC('$1'), '$1', '$3'}.
expr -> expr '<' expr : {first('$2'), ?LOC('$1'), '$1', '$3'}.
expr -> expr '>=' expr : {first('$2'), ?LOC('$1'), '$1', '$3'}.
expr -> expr '<=' expr : {first('$2'), ?LOC('$1'), '$1', '$3'}.
expr -> expr '+' expr : {first('$2'), ?LOC('$1'), '$1', '$3'}.
expr -> expr '-' expr : {first('$2'), ?LOC('$1'), '$1', '$3'}.
expr -> expr mul expr : {first('$2'), ?LOC('$1'), '$1', '$3'}.
expr -> expr '/' expr : {first('$2'), ?LOC('$1'), '$1', '$3'}.
expr -> expr '%' expr : {first('$2'), ?LOC('$1'), '$1', '$3'}.
expr -> expr '++' expr : {first('$2'), ?LOC('$1'), '$1', '$3'}.
expr -> expr '--' expr : {first('$2'), ?LOC('$1'), '$1', '$3'}.
expr -> expr '.' var : {field, ?LOC('$1'), '$1', '$3'}.
expr -> expr '.' con_token : {field, ?LOC('$1'), '$1', '$3'}.
expr -> '[' expr_list '|' expr ']' : {cons, ?LOC('$1'), '$2', '$4'}.
expr -> '!' expr : {first('$1'), ?LOC('$1'), '$2'}.
expr -> '#' expr : {first('$1'), ?LOC('$1'), '$2'}.
expr -> '$' expr : {first('$1'), ?LOC('$1'), '$2'}.
expr -> neg : '$1'.
expr -> lam : '$1'.
expr -> discard expr : {first('$1'), ?LOC('$1'), '$2'}.
expr -> expr '::' te : {first('$2'), ?LOC('$1'), '$1', '$3'}.
expr -> expr '(' ')' :
  flatten_app({app, ?LOC('$1'), '$1', [{none, ?LOC('$2')}]}).
expr -> expr '(' expr_list ')' : flatten_app({app, ?LOC('$1'), '$1', '$3'}).
expr -> atom ':' var '(' ')' :
  {app, ?LOC('$1'), {native, ?LOC('$1'), '$1', '$3', 0},
    [{none, ?LOC('$4')}]}.
expr -> atom ':' var '(' expr_list ')' :
  {app, ?LOC('$1'), {native, ?LOC('$1'), '$1', '$3', num_args('$5')}, '$5'}.
expr -> atom ':' var '/' int :
  {native, ?LOC('$1'), '$1', '$3', element(3, '$5')}.
expr -> if expr then expr :
  {first('$1'), ?LOC('$1'), '$2', '$4', {none, ?LOC('$3')}}.
expr -> if expr then expr else expr :
  {first('$1'), ?LOC('$1'), '$2', '$4', '$6'}.
expr -> let let_list in expr : {first('$1'), ?LOC('$1'), '$2', '$4'}.
expr -> if let let_init then expr :
  {if_let, ?LOC('$1'), '$3', '$5', {none, ?LOC('$5')}}.
expr -> if let let_init then expr else expr :
  {if_let, ?LOC('$1'), '$3', '$5', '$7'}.
expr -> match expr start_match match_list '}' :
  {first('$1'), ?LOC('$1'), '$2', '$4'}.
expr -> '{' semi_list '}' : {block, ?LOC('$1'), '$2'}.

expr_list -> expr : ['$1'].
expr_list -> expr ',' expr_list : ['$1' | '$3'].

kv_list -> expr '=>' expr : [{'$1', '$3'}].
kv_list -> expr '=>' expr ',' kv_list : [{'$1', '$3'} | '$5'].

start_record -> '{' : '$1'.

init_list -> var '=' expr : [{'$1', '$3'}].
init_list -> var '=' expr ',' init_list : [{'$1', '$3'} | '$5'].

% * also used in pattern matching for different purpose, so we factor this out
% to avoid precendence leaking
mul -> '*' : '$1'.

neg -> '-' expr : {first('$1'), ?LOC('$1'), '$2'}.

lam -> '|' '-' '|' expr : {fn, ?LOC('$1'), [], '$4'}.
lam -> '|' var_list '|' expr : {fn, ?LOC('$1'), '$2', '$4'}.

let_list -> let_init : ['$1'].
let_list -> let_init ',' let_list : ['$1' | '$3'].

let_init -> pattern '=' expr : {'$1', '$3'}.
let_init -> var '(' ')' '=' expr : {'$1', {fn, ?LOC('$1'), [], '$5'}}.
let_init -> var '(' var_list ')' '=' expr :
  {'$1', {fn, ?LOC('$1'), '$3', '$6'}}.

start_match -> '{' : '$1'.

match_list -> pattern '=>' expr : [{'$1', '$3'}].
match_list -> pattern '=>' expr ',' match_list : [{'$1', '$3'} | '$5'].

semi_list -> expr : ['$1'].
semi_list -> expr ';' semi_list : ['$1' | '$3'].

pattern -> int : '$1'.
pattern -> float : '$1'.
pattern -> bool : '$1'.
pattern -> char : '$1'.
pattern -> str : '$1'.
pattern -> atom : '$1'.
pattern -> var : '$1'.
pattern -> '*' var : setelement(1, '$2', var_value).
pattern -> '_' : '$1'.
pattern -> pattern_con : '$1'.
pattern -> pattern_con '(' pattern_list ')' : {app, ?LOC('$1'), '$1', '$3'}.
pattern -> '[' ']' : {list, ?LOC('$1'), []}.
pattern -> '[' pattern_list ']' : {list, ?LOC('$1'), '$2'}.
pattern -> '[' pattern_list '|' pattern ']' :
  {cons, ?LOC('$1'), '$2', '$4'}.
pattern -> '(' pattern ',' pattern_list ')' :
  {tuple, ?LOC('$1'), ['$2' | '$4']}.
pattern -> '(' pattern ')' : '$2'.

pattern_con -> con_token : '$1'.
pattern_con -> con_token '.' con_token : {field, ?LOC('$1'), '$1', '$3'}.

pattern_list -> pattern : ['$1'].
pattern_list -> pattern ',' pattern_list : ['$1' | '$3'].

te -> '(' ')' : {none, ?LOC('$1')}.
te -> te_con : '$1'.
te -> tv_token : tv_te('$1').
te -> tv_token ':' te_con : tv_te('$1', '$3').
te -> te_con '<' te_list '>' : {gen_te, ?LOC('$1'), '$1', '$3'}.
te -> '[' te ']' :
  {gen_te, ?LOC('$1'), {con_token, ?LOC('$1'), "List"}, ['$2']}.
te -> '(' te ',' te_list ')' : {tuple_te, ?LOC('$1'), ['$2' | '$4']}.
te -> '(' te ')' : '$2'.
te -> '{' field_list '}' : {record_te, ?LOC('$1'), '$2'}.
te -> '{' tv_token '|' field_list '}' :
  {record_ext_te, ?LOC('$1'), tv_te('$2'), '$4'}.
te -> te '->' te : {lam_te, ?LOC('$1'), '$1', '$3'}.

te_con -> con_token : '$1'.
te_con -> con_token '.' con_token : qualify('$1', '$3').

te_list -> te : ['$1'].
te_list -> te ',' te_list : ['$1' | '$3'].

enum -> enum_token con_token '{' option_list '}' :
  {first('$1'), ?LOC('$1'), '$2', '$4'}.
enum -> enum_token con_token '<' tv_list '>' '{' option_list '}' :
  {first('$1'), ?LOC('$1'), {gen_te, ?LOC('$2'), '$2', '$4'}, '$7'}.

option_list -> option : ['$1'].
option_list -> option ',' option_list : ['$1' | '$3'].

option -> con_token : {'$1', [], default}.
option -> con_token atom : {'$1', [], '$2'}.
option -> con_token '(' te_list ')' : {'$1', '$3', default}.
option -> con_token '(' te_list ')' atom : {'$1', '$3', '$5'}.

struct -> struct_token con_token '{' field_list '}' :
  {first('$1'), ?LOC('$1'), '$2', {record_te, ?LOC('$3'), '$4'}}.
struct -> struct_token con_token '<' tv_list '>' '{' field_list '}' :
  {first('$1'), ?LOC('$1'), {gen_te, ?LOC('$2'), '$2', '$4'},
    {record_te, ?LOC('$6'), '$7'}}.

field_list -> field : ['$1'].
field_list -> field ',' field_list : ['$1' | '$3'].

field -> var '::' te : {'$1', '$3'}.

tv_list -> tv_token : [tv_te('$1')].
tv_list -> tv_token ',' tv_list : [tv_te('$1') | '$3'].

Nonassoc 10 '='.
Right 20 '->'.
Left 30 '|>'.
Unary 40 lam.
Left 50 '||'.
Left 60 '&&'.
Nonassoc 70 '==' '!=' '>' '<' '>=' '<='.
Left 80 '+' '-' '++' '--'.
Left 90 mul '/' '%'.
Nonassoc 100 '::'.
Unary 110 '!' '#' '$' neg 'discard'.
Nonassoc 120 '('.
Nonassoc 130 '.'.

Nonassoc 10 'then'.
Nonassoc 20 'else'.

Nonassoc 10 start_match.
Nonassoc 20 start_record.

Erlang code.

-include("errors.hrl").

first(Node) -> element(1, Node).

num_args([]) -> 0;
num_args([{none, _}]) -> 0;
num_args(Args) -> length(Args).

flatten_app({app, _, {app, _, _, _}=App, Args}) ->
  {app, Line, Expr, InitialArgs} = flatten_app(App),
  {app, Line, Expr, InitialArgs ++ Args};
flatten_app(Node) -> Node.

tv_te({tv_token, Line, Name}) ->
  {tv_te, Line, Name, {none, Line}}.

tv_te({tv_token, Line, Name}, TE) ->
  {tv_te, Line, Name, TE}.

qualify({con_token, Line, Mod}, {con_token, _, Con}) ->
  {con_token, Line, lists:concat([Mod, '.', Con])}.
