Nonterminals
  prg decl sig
  type type_list
  expr lam neg maybe_else
  var_list expr_list init_list kv_list.
Terminals
  '=' '(' ')' ','
  '==' '!=' '||' '&&' '!' '>' '<' '>=' '<='
  '+' '-' '*' '/'
  '++' '--' '|' '::' ':' '->'
  if then else let in
  int float bool str atom var
  '[' ']' '{' '}' '=>' '#'
  sig_tv sig_con.
Rootsymbol prg.

prg -> '$empty' : [].
prg -> decl prg : ['$1' | '$2'].
prg -> var sig prg : [{sig, '$1', '$2'} | '$3'].

decl -> var '=' expr : {global, '$1', '$3'}.
decl -> var '(' ')' '=' expr : {global, '$1', {fn, [], '$5'}}.
decl -> var '(' var_list ')' '=' expr : {global, '$1', {fn, '$3', '$6'}}.

sig -> '::' type : '$2'.

type -> '(' ')' : none.
type -> sig_con : '$1'.
type -> sig_tv : '$1'.
type -> sig_tv ':' sig_con : {sig_iface, '$1', '$3'}.
type -> sig_con '<' type_list '>' : {sig_gen, '$1', '$3'}.
type -> '[' type ']' : {sig_gen, {sig_con, element(2, '$1'), "List"}, '$2'}.
type -> '(' type ',' type_list ')' : {sig_tuple, '$2', '$4'}.
type -> '(' type ')' : '$2'.
type -> type '->' type : {sig_lam, '$1', '$3'}.

type_list -> type : '$1'.
type_list -> type ',' type_list : {sig_tuple, '$1', '$3'}.

expr -> '(' ')' : none.
expr -> int : '$1'.
expr -> float : '$1'.
expr -> bool : '$1'.
expr -> str : '$1'.
expr -> atom : '$1'.
expr -> var : '$1'.
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
Unary 110 '!' neg '#'.
Unary 120 '('.

Erlang code.

num_args([]) -> 0;
num_args([none]) -> 0;
num_args(Args) -> length(Args).
