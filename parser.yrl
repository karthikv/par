Nonterminals
  prg decl sig type type_list expr
  eq_op neq_op or_op and_op gt_op lt_op gte_op lte_op
  add_op sub_op mul_op div_op
  con_op sep_op
  not_op neg_op set_op
  var_list expr_list init_list kv_list
  maybe_else.
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

decl -> var '=' expr : {set, '$1', '$3'}.
decl -> var '(' ')' '=' expr : {fn, '$1', [], '$5'}.
decl -> var '(' var_list ')' '=' expr : {fn, '$1', '$3', '$6'}.

sig -> '::' type : '$2'.

type -> '(' ')' : none.
type -> sig_con : '$1'.
type -> sig_tv : '$1'.
type -> sig_tv ':' sig_con : {sig_iface, '$1', '$3'}.
type -> sig_con lt_op type_list '>' : {sig_gen, '$1', '$3'}.
type -> '[' type ']' : {sig_gen, {sig_con, element(2, '$1'), "List"}, '$2'}.
type -> '(' type ',' type_list ')' : {sig_tuple, '$2', '$4'}.
type -> '(' type ')' : '$2'.
type -> type '->' type : {sig_lam, '$1', '$3'}.

type_list -> type : '$1'.
type_list -> type ',' type_list : {sig_tuple, '$1', '$3'}.

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
expr -> expr eq_op expr : {'$2', '$1', '$3'}.
expr -> expr neq_op expr : {'$2', '$1', '$3'}.
expr -> expr or_op expr : {'$2', '$1', '$3'}.
expr -> expr and_op expr : {'$2', '$1', '$3'}.
expr -> expr gt_op expr : {'$2', '$1', '$3'}.
expr -> expr lt_op expr : {'$2', '$1', '$3'}.
expr -> expr gte_op expr : {'$2', '$1', '$3'}.
expr -> expr lte_op expr : {'$2', '$1', '$3'}.
expr -> expr add_op expr : {'$2', '$1', '$3'}.
expr -> expr sub_op expr : {'$2', '$1', '$3'}.
expr -> expr mul_op expr : {'$2', '$1', '$3'}.
expr -> expr div_op expr : {'$2', '$1', '$3'}.
expr -> expr con_op expr : {'$2', '$1', '$3'}.
expr -> expr sep_op expr : {'$2', '$1', '$3'}.
expr -> not_op expr : {'$1', '$2'}.
expr -> neg_op expr : {'$1', '$2'}.
expr -> set_op expr : {'$1', '$2'}.
expr -> expr sig : {expr_sig, '$1', '$2'}.
expr -> '(' expr ')' : '$2'.
expr -> expr '(' ')' : {app, '$1', []}.
expr -> expr '(' expr_list ')' : {app, '$1', '$3'}.
expr -> atom ':' var '(' ')' : {app, {native, '$1', '$3', 0}, []}.
expr -> atom ':' var '(' expr_list ')' :
  {app, {native, '$1', '$3', length('$5')}, '$5'}.
expr -> atom ':' var '/' int : {native, '$1', '$3', element(3, '$5')}.
expr -> if expr then expr maybe_else : {'$1', '$2', '$4', '$5'}.
expr -> let init_list in expr : {'$1', '$2', '$4'}.
expr -> '|' '-' '|' expr : {fn, none, [], '$4'}.
expr -> '|' var_list '|' expr : {fn, none, '$2', '$4'}.

eq_op -> '==' : '$1'.
neq_op -> '!=' : '$1'.
or_op -> '||' : '$1'.
and_op -> '&&' : '$1'.
gt_op -> '>' : '$1'.
lt_op -> '<' : '$1'.
gte_op -> '>=' : '$1'.
lte_op -> '<=' : '$1'.
add_op -> '+' : '$1'.
sub_op -> '-' : '$1'.
mul_op -> '*' : '$1'.
div_op -> '/' : '$1'.
con_op -> '++' : '$1'.
sep_op -> '--' : '$1'.

not_op -> '!' : '$1'.
neg_op -> '-' : '$1'.
set_op -> '#' : '$1'.

var_list -> var : ['$1'].
var_list -> var ',' var_list : ['$1' | '$3'].

expr_list -> expr : ['$1'].
expr_list -> expr ',' expr_list : ['$1' | '$3'].

init_list -> var '=' expr : [{'$1', '$3'}].
init_list -> var '=' expr ',' init_list : [{'$1', '$3'} | '$5'].

kv_list -> expr '=>' expr : [{'$1', '$3'}].
kv_list -> expr '=>' expr ',' kv_list : [{'$1', '$3'} | '$5'].

maybe_else -> '$empty' : none.
maybe_else -> else expr : '$2'.

Nonassoc 10 '='.
Right 20 '->'.
Right 30 'else'.
Left 40 or_op.
Left 50 and_op.
Nonassoc 60 eq_op neq_op gt_op lt_op gte_op lte_op.
Left 70 add_op sub_op con_op sep_op.
Left 80 mul_op div_op.
Unary 90 '::'.
Unary 100 not_op neg_op set_op.
Unary 110 '('.
