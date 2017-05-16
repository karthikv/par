Nonterminals
  prg global var_list
  expr con_var expr_list expr_list_tuple
  kv_list start_record init_list mul neg lam
  maybe_else semi_list
  let_list start_match match_list
  pattern pattern_list pattern_list_tuple
  sig te te_list_tuple
  enum option_list option te_list
  struct field_list field tv_list_tuple.

Terminals
  '=' '(' ')' ','
  '==' '!=' '||' '&&' '!' '>' '<' '>=' '<='
  '+' '-' '*' '/' '%'
  '++' '--' '|' '::' ':' '->' ';' 'discard'
  if then else let in match
  enum_token struct_token
  int float bool str atom var '_'
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

var_list -> var : ['$1'].
var_list -> var ',' var_list : ['$1' | '$3'].

expr -> '(' ')' : none.
expr -> int : '$1'.
expr -> float : '$1'.
expr -> bool : '$1'.
expr -> str : '$1'.
expr -> atom : '$1'.
expr -> var : '$1'.
expr -> con_var : '$1'.
expr -> '[' ']' : {list, []}.
expr -> '[' expr_list ']' : {list, '$2'}.
expr -> '(' expr ',' expr_list_tuple ')' : {tuple, '$2', '$4'}.
expr -> '(' expr ')' : '$2'.
expr -> '{' '}' : {map, []}.
expr -> '{' kv_list '}' : {map, '$2'}.
expr -> con_var start_record init_list '}' : {record, '$1', '$3'}.
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
expr -> expr mul expr : {'$2', '$1', '$3'}.
expr -> expr '/' expr : {'$2', '$1', '$3'}.
expr -> expr '%' expr : {'$2', '$1', '$3'}.
expr -> expr '++' expr : {'$2', '$1', '$3'}.
expr -> expr '--' expr : {'$2', '$1', '$3'}.
expr -> '!' expr : {'$1', '$2'}.
expr -> '#' expr : {'$1', '$2'}.
expr -> neg : '$1'.
expr -> lam : '$1'.
expr -> discard expr : {'$1', '$2'}.
expr -> expr sig : {expr_sig, '$1', '$2'}.
expr -> expr '(' ')' : {app, '$1', []}.
expr -> expr '(' expr_list ')' : {app, '$1', '$3'}.
expr -> atom ':' var '(' ')' : {app, {native, '$1', '$3', 0}, []}.
expr -> atom ':' var '(' expr_list ')' :
  {app, {native, '$1', '$3', num_args('$5')}, '$5'}.
expr -> atom ':' var '/' int : {native, '$1', '$3', element(3, '$5')}.
expr -> if expr then expr maybe_else : {'$1', '$2', '$4', '$5'}.
expr -> if let pattern '=' expr then expr maybe_else :
  {setelement(1, '$1', if_let), '$3', '$5', '$7', '$8'}.
expr -> let let_list in expr : {'$1', '$2', '$4'}.
expr -> match expr start_match match_list '}' : {'$1', '$2', '$4'}.
expr -> '{' semi_list '}' : {block, '$2'}.

con_var -> con_token : setelement(1, '$1', con_var).

expr_list -> expr : ['$1'].
expr_list -> expr ',' expr_list : ['$1' | '$3'].

expr_list_tuple -> expr : '$1'.
expr_list_tuple -> expr ',' expr_list_tuple : {tuple, '$1', '$3'}.

kv_list -> expr '=>' expr : [{'$1', '$3'}].
kv_list -> expr '=>' expr ',' kv_list : [{'$1', '$3'} | '$5'].

start_record -> '{' : '$1'.

init_list -> var '=' expr : [{'$1', '$3'}].
init_list -> var '=' expr ',' init_list : [{'$1', '$3'} | '$5'].

% * also used in pattern matching for different purpose, so we factor this out
% to avoid precendence leaking
mul -> '*' : '$1'.

neg -> '-' expr : {'$1', '$2'}.

lam -> '|' '-' '|' expr : {fn, [], '$4'}.
lam -> '|' var_list '|' expr : {fn, '$2', '$4'}.

maybe_else -> '$empty' : none.
maybe_else -> else expr : '$2'.

semi_list -> expr : ['$1'].
semi_list -> expr ';' semi_list : ['$1' | '$3'].

let_list -> pattern '=' expr : [{'$1', '$3'}].
let_list -> pattern '=' expr ',' let_list : [{'$1', '$3'} | '$5'].

start_match -> '{' : '$1'.

match_list -> pattern '=>' expr : [{'$1', '$3'}].
match_list -> pattern '=>' expr ',' match_list : [{'$1', '$3'} | '$5'].

pattern -> int : '$1'.
pattern -> float : '$1'.
pattern -> bool : '$1'.
pattern -> str : '$1'.
pattern -> atom : '$1'.
pattern -> var : '$1'.
pattern -> '*' var : setelement(1, '$2', var_value).
pattern -> '_' : '$1'.
pattern -> con_var : '$1'.
pattern -> con_var '(' pattern_list ')' : {app, '$1', '$3'}.
pattern -> '[' ']' : {list, []}.
pattern -> '[' pattern_list ']' : {list, '$2'}.
pattern -> '[' pattern_list '|' pattern ']' : {list, '$2', '$4'}.
pattern -> '(' pattern ',' pattern_list_tuple ')' : {tuple, '$2', '$4'}.
pattern -> '(' pattern ')' : '$2'.

pattern_list -> pattern : ['$1'].
pattern_list -> pattern ',' pattern_list : ['$1' | '$3'].

pattern_list_tuple -> pattern : '$1'.
pattern_list_tuple -> pattern ',' pattern_list_tuple : {tuple, '$1', '$3'}.

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

Nonassoc 10 '='.
Right 20 '->'.
Unary 30 lam.
Right 40 'else'.
Left 50 '||'.
Left 60 '&&'.
Nonassoc 70 '==' '!=' '>' '<' '>=' '<='.
Left 80 '+' '-' '++' '--'.
Left 90 mul '/' '%'.
Unary 100 '::'.
Unary 110 '!' '#' neg 'discard'.
Unary 120 '('.

Nonassoc 10 start_match.
Nonassoc 20 start_record.

Erlang code.

num_args([]) -> 0;
num_args([none]) -> 0;
num_args(Args) -> length(Args).
