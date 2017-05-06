Nonterminals
  prg global sig
  t t_list_tuple enum option_list option t_list tv_list
  expr lam neg maybe_else
  var_list expr_list init_list kv_list semi_list.

Terminals
  '=' '(' ')' ','
  '==' '!=' '||' '&&' '!' '>' '<' '>=' '<='
  '+' '-' '*' '/'
  '++' '--' '|' '::' ':' '->' ';' 'discard'
  if then else let in
  enum_token int float bool str atom var
  '[' ']' '{' '}' '=>' '#'
  tv_token con_token.

Rootsymbol prg.


prg -> '$empty' : [].
prg -> global prg : ['$1' | '$2'].
prg -> var sig prg : [{sig, '$1', '$2'} | '$3'].
prg -> enum prg : ['$1' | '$2'].

global -> var '=' expr : {global, '$1', '$3'}.
global -> var '(' ')' '=' expr : {global, '$1', {fn, [], '$5'}}.
global -> var '(' var_list ')' '=' expr : {global, '$1', {fn, '$3', '$6'}}.

sig -> '::' t : '$2'.

t -> '(' ')' : none.
t -> con_token : '$1'.
t -> tv_token : '$1'.
t -> tv_token ':' con_token : {iface_expr, '$1', '$3'}.
t -> con_token '<' t_list_tuple '>' : {gen_expr, '$1', '$3'}.
t -> '[' t ']' : {gen_expr, {con_token, element(2, '$1'), "List"}, '$2'}.
t -> '(' t ',' t_list_tuple ')' : {tuple_expr, '$2', '$4'}.
t -> '(' t ')' : '$2'.
t -> t '->' t : {lam_expr, '$1', '$3'}.

t_list_tuple -> t : '$1'.
t_list_tuple -> t ',' t_list_tuple : {tuple_expr, '$1', '$3'}.

enum -> enum_token con_token '{' option_list '}' : {enum, '$2', '$4'}.
enum -> enum_token con_token '<' tv_list '>' '{' option_list '}' :
  {enum, {gen_expr, '$2', '$4'}, '$7'}.

option_list -> option : ['$1'].
option_list -> option ',' option_list : ['$1' | '$3'].

option -> con_token : {option, '$1', []}.
option -> con_token '(' t_list ')' : {option, '$1', '$3'}.

t_list -> t : ['$1'].
t_list -> t ',' t_list : ['$1' | '$3'].

tv_list -> tv_token : ['$1'].
tv_list -> tv_token ',' tv_list : ['$1' | '$3'].

expr -> '(' ')' : none.
expr -> int : '$1'.
expr -> float : '$1'.
expr -> bool : '$1'.
expr -> str : '$1'.
expr -> atom : '$1'.
expr -> var : '$1'.
expr -> con_token : {var, element(2, '$1'), element(3, '$1')}.
expr -> '[' ']' : {list, []}.
expr -> '[' expr_list ']' : {list, '$2'}.
expr -> '(' expr ',' expr_list ')' : {tuple, ['$2' | '$4']}.
expr -> '{' '}' : {map, []}.
expr -> '{' kv_list '}' : {map, '$2'}.
expr -> expr '==' expr : {'$2', '$1', '$3'}.
expr -> expr '!=' expr : {'$2', '$1', '$3'}.
expr -> expr '||' expr : {'$2', '$1', '$3'}.
expr -> expr '&&' expr : {'$2', '$1', '$3'}.
expr -> expr '>' expr : {'$2', '$1', '$3'}.
expr -> expr '<' expr : {'$2', '$1', '$3'}.
expr -> expr '>=' expr : {'$2', '$1', '$3'}.
expr -> expr '<=' expr : {'$2', '$1', '$3'}.
expr -> expr '+' expr : {'$2', '$1', '$3'}.
expr -> expr '-' expr : {'$2', '$1', '$3'}.
expr -> expr '*' expr : {'$2', '$1', '$3'}.
expr -> expr '/' expr : {'$2', '$1', '$3'}.
expr -> expr '++' expr : {'$2', '$1', '$3'}.
expr -> expr '--' expr : {'$2', '$1', '$3'}.
expr -> '!' expr : {'$1', '$2'}.
expr -> '#' expr : {'$1', '$2'}.
expr -> neg : '$1'.
expr -> discard expr : {'$1', '$2'}.
expr -> expr sig : {expr_sig, '$1', '$2'}.
expr -> '(' expr ')' : '$2'.
expr -> expr '(' ')' : {app, '$1', []}.
expr -> expr '(' expr_list ')' : {app, '$1', '$3'}.
expr -> atom ':' var '(' ')' : {app, {native, '$1', '$3', 0}, []}.
expr -> atom ':' var '(' expr_list ')' :
  {app, {native, '$1', '$3', num_args('$5')}, '$5'}.
expr -> atom ':' var '/' int : {native, '$1', '$3', element(3, '$5')}.
expr -> if expr then expr maybe_else : {'$1', '$2', '$4', '$5'}.
expr -> let init_list in expr : {'$1', '$2', '$4'}.
expr -> '{' semi_list '}' : {block, '$2'}.
expr -> lam : '$1'.

lam -> '|' '-' '|' expr : {fn, [], '$4'}.
lam -> '|' var_list '|' expr : {fn, '$2', '$4'}.

neg -> '-' expr : {'$1', '$2'}.

maybe_else -> '$empty' : none.
maybe_else -> else expr : '$2'.

var_list -> var : ['$1'].
var_list -> var ',' var_list : ['$1' | '$3'].

expr_list -> expr : ['$1'].
expr_list -> expr ',' expr_list : ['$1' | '$3'].

init_list -> var '=' expr : [{'$1', '$3'}].
init_list -> var '=' expr ',' init_list : [{'$1', '$3'} | '$5'].

kv_list -> expr '=>' expr : [{'$1', '$3'}].
kv_list -> expr '=>' expr ',' kv_list : [{'$1', '$3'} | '$5'].

semi_list -> expr : ['$1'].
semi_list -> expr ';' semi_list : ['$1' | '$3'].


Nonassoc 10 '='.
Right 20 '->'.
Unary 30 lam.
Right 40 'else'.
Left 50 '||'.
Left 60 '&&'.
Nonassoc 70 '==' '!=' '>' '<' '>=' '<='.
Left 80 '+' '-' '++' '--'.
Left 90 '*' '/'.
Unary 100 '::'.
Unary 110 '!' '#' neg 'discard'.
Unary 120 '('.


Erlang code.

num_args([]) -> 0;
num_args([none]) -> 0;
num_args(Args) -> length(Args).
