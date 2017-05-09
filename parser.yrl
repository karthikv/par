Nonterminals
  prg global sig te te_list_tuple
  enum option_list option te_list
  struct field_list field tv_list_tuple
  expr lam neg maybe_else
  var_list expr_list init_list kv_list semi_list.

Terminals
  '=' '(' ')' ','
  '==' '!=' '||' '&&' '!' '>' '<' '>=' '<='
  '+' '-' '*' '/' '%'
  '++' '--' '|' '::' ':' '->' ';' 'discard'
  if then else let in
  enum_token struct_token
  int float bool str atom var
  '[' ']' '{' '}' '=>' '#'
  tv_token con_token.

Rootsymbol prg.

prg -> '$empty' : [].
prg -> global prg : ['$1' | '$2'].
prg -> var sig prg : [{sig, '$1', '$2'} | '$3'].
prg -> enum prg : ['$1' | '$2'].
prg -> struct prg : ['$1' | '$2'].

global -> var '=' expr : {global, '$1', '$3'}.
global -> var '(' ')' '=' expr : {global, '$1', {fn, [], '$5'}}.
global -> var '(' var_list ')' '=' expr : {global, '$1', {fn, '$3', '$6'}}.

sig -> '::' te : '$2'.

te -> '(' ')' : none.
te -> con_token : '$1'.
te -> tv_token : '$1'.
te -> tv_token ':' con_token : {iface_te, '$1', '$3'}.
te -> con_token '<' te_list_tuple '>' : {gen_te, '$1', '$3'}.
te -> '[' te ']' : {gen_te, {con_token, element(2, '$1'), "List"}, '$2'}.
te -> '(' te ',' te_list_tuple ')' : {tuple_te, '$2', '$4'}.
te -> '(' te ')' : '$2'.
te -> te '->' te : {lam_te, '$1', '$3'}.

te_list_tuple -> te : '$1'.
te_list_tuple -> te ',' te_list_tuple : {tuple_te, '$1', '$3'}.

enum -> enum_token con_token '{' option_list '}' : {enum, '$2', '$4'}.
enum -> enum_token con_token '<' tv_list_tuple '>' '{' option_list '}' :
  {enum, {gen_te, '$2', '$4'}, '$7'}.

option_list -> option : ['$1'].
option_list -> option ',' option_list : ['$1' | '$3'].

option -> con_token : {option, '$1', []}.
option -> con_token '(' te_list ')' : {option, '$1', '$3'}.

te_list -> te : ['$1'].
te_list -> te ',' te_list : ['$1' | '$3'].

struct -> struct_token con_token '{' field_list '}' : {struct, '$2', '$4'}.
struct -> struct_token con_token '<' tv_list_tuple '>' '{' field_list '}' :
  {struct, {gen_te, '$2', '$4'}, '$7'}.

field_list -> field : ['$1'].
field_list -> field ',' field_list : ['$1' | '$3'].

field -> var sig : {field, '$1', '$2'}.

tv_list_tuple -> tv_token : '$1'.
tv_list_tuple -> tv_token ',' tv_list_tuple : {tuple_te, '$1', '$3'}.

expr -> '(' ')' : none.
expr -> int : '$1'.
expr -> float : '$1'.
expr -> bool : '$1'.
expr -> str : '$1'.
expr -> atom : '$1'.
expr -> var : '$1'.
expr -> con_token : con_to_var('$1').
expr -> '[' ']' : {list, []}.
expr -> '[' expr_list ']' : {list, '$2'}.
expr -> '(' expr ',' expr_list ')' : {tuple, ['$2' | '$4']}.
expr -> '{' '}' : {map, []}.
expr -> '{' kv_list '}' : {map, '$2'}.
expr -> con_token '{' init_list '}' : {record, con_to_var('$1'), '$3'}.
expr -> var '{' init_list '}' : {update_record, '$1', '$3'}.
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
expr -> expr '%' expr : {'$2', '$1', '$3'}.
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
Left 90 '*' '/' '%'.
Unary 100 '::'.
Unary 110 '!' '#' neg 'discard'.
Unary 120 '('.

Erlang code.

num_args([]) -> 0;
num_args([none]) -> 0;
num_args(Args) -> length(Args).

con_to_var({con_token, Line, Name}) -> {var, Line, Name}.
