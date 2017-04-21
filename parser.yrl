Nonterminals prg decl expr neg var_list expr_list init_list maybe_else.
Terminals
  '=' '(' ')' ','
  '==' '!=' '||' '&&' '!' '>' '<' '>=' '<='
  '+' '-' '*' '/'
  '++' '|'
  if then else let in
  int float bool str var.
Rootsymbol prg.

prg -> decl : ['$1'].
prg -> decl prg : ['$1'|'$2'].

decl -> var '=' expr : {set, '$1', '$3'}.
decl -> var '(' ')' '=' expr : {fn, '$1', [], '$5'}.
decl -> var '(' var_list ')' '=' expr : {fn, '$1', '$3', '$6'}.

expr -> int : '$1'.
expr -> float : '$1'.
expr -> bool : '$1'.
expr -> str : '$1'.
expr -> var : '$1'.
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
expr -> '!' expr : {'$1', '$2'}.
expr -> neg : '$1'.
expr -> '(' expr ')' : '$2'.
expr -> var '(' ')' : {app, '$1', []}.
expr -> var '(' expr_list ')' : {app, '$1', '$3'}.
expr -> if expr then expr maybe_else : {'$1', '$2', '$4', '$5'}.
expr -> let init_list in expr : {'$1', '$2', '$4'}.
expr -> '|' '-' '|' expr : {fn, none, [], '$4'}.
expr -> '|' var_list '|' expr : {fn, none, '$2', '$4'}.

neg -> '-' expr : {'$1', '$2'}.

var_list -> var : ['$1'].
var_list -> var ',' var_list : ['$1'|'$3'].

expr_list -> expr : ['$1'].
expr_list -> expr ',' expr_list : ['$1'|'$3'].

init_list -> var '=' expr : [{'$1', '$3'}].
init_list -> var '=' expr ',' init_list : [{'$1', '$3'}|'$5'].

maybe_else -> '$empty' : none.
maybe_else -> else expr : '$2'.

Nonassoc 100 '='.
Right 200 'else'.
Left 300 '||'.
Left 400 '&&'.
Nonassoc 500 '==' '!=' '>' '<' '>=' '<='.
Left 600 '+' '-' '++'.
Left 700 '*' '/'.
Unary 800 '!' neg.
