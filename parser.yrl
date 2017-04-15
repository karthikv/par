Nonterminals prg decl varlist expr exprlist.
Terminals if then else '=' '(' ')' ',' '+' int bool var.
Rootsymbol prg.

prg -> decl : ['$1'].
prg -> decl prg : ['$1'|'$2'].

decl -> var '=' expr : {set, '$1', '$3'}.
decl -> var '(' ')' '=' expr : {fn, '$1', [], '$5'}.
decl -> var '(' varlist ')' '=' expr : {fn, '$1', '$3', '$6'}.

varlist -> var : ['$1'].
varlist -> var ',' varlist : ['$1'|'$3'].

expr -> int : '$1'.
expr -> bool : '$1'.
expr -> var : '$1'.
expr -> var '(' ')' : {app, '$1', []}.
expr -> var '(' exprlist ')' : {app, '$1', '$3'}.
expr -> expr '+' expr : {'$2', '$1', '$3'}.
expr -> '(' expr ')' : '$2'.
expr -> if expr then expr : {'$1', '$2', '$4'}.
expr -> if expr then expr else expr : {'$1', '$2', '$4', '$6'}.

exprlist -> expr : ['$1'].
exprlist -> expr ',' exprlist : ['$1'|'$3'].

Left 100 '+'.
