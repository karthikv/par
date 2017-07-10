-ifndef(ERRORS_HRL_).
-define(ERRORS_HRL_, 1).

-define(FMT(Str), lists:flatten(io_lib:format(Str, []))).
-define(FMT(Str, Args), lists:flatten(io_lib:format(Str, Args))).
-define(ERR(Str), io:format(standard_error, Str, [])).
-define(ERR(Str, Args), io:format(standard_error, Str, Args)).

-define(FROM_GLOBAL_DEF(Name), ?FMT("global definition of ~s", [Name])).
-define(FROM_GLOBAL_SIG, "global type signature").
-define(FROM_EXPR_SIG, "expression type signature").
-define(FROM_ENUM_CTOR, "enum constructor").
-define(FROM_STRUCT_CTOR, "struct constructor").
-define(FROM_LIST_ELEM, "element in list literal").
-define(FROM_LIST_TAIL, "list tail").
-define(FROM_MAP_KEY, "key in map literal").
-define(FROM_MAP_VALUE, "value in map literal").
-define(FROM_RECORD_UPDATE, "updating record").
-define(FROM_RECORD_CREATE(Name), ?FMT("creating record ~s", [Name])).
-define(FROM_FIELD_ACCESS(Name), ?FMT("accessing field ~s", [Name])).
-define(FROM_APP, "function call").
-define(FROM_IF_COND, "if condition").
-define(FROM_IF_BODY, "if/else body").
-define(FROM_LET, "let pattern").
-define(FROM_IF_LET_PATTERN, "if-let pattern").
-define(FROM_IF_LET_BODY, "if-let/else body").
-define(FROM_MATCH_PATTERN, "match pattern").
-define(FROM_MATCH_BODY, "match body").
-define(FROM_OP(Op), ?FMT("~p operator", [Op])).

-define(ERR_REDEF(Name), ?FMT("~s is already defined", [Name])).
-define(
  ERR_REDEF_TYPE(Con),
  ?FMT("type ~s is already defined", [utils:unqualify(Con)])
).
-define(
  ERR_REDEF_BUILTIN_TYPE(Con),
  ?FMT("~s is already defined as a builtin type", [utils:unqualify(Con)])
).
-define(
  ERR_REDEF_TV(Con),
  ?FMT("type variable ~s is already defined", [utils:unqualify(Con)]
)).
-define(
  ERR_REDEF_MODULE(Module),
  ?FMT("module ~s is already defined", [Module])
).
-define(
  ERR_SIG_NO_DEF(Name),
  ?FMT("expected ~s to be defined after its signature", [Name])
).
-define(ERR_DUP_FIELD(Name), ?FMT("duplicate field ~s in this record", [Name])).
-define(
  ERR_TV_SCOPE(V, Con),
  ?FMT(
    "type variable ~s isn't in scope; "
    "it must be defined as a parameter to type ~s",
    [V, utils:unqualify(Con)]
  )
).
-define(
  ERR_TV_IFACE(V, Exp, Actual),
  ?FMT(
    "type variable ~s was previously given interface ~s, "
    "but now has interface ~s; the two must be consistent",
    [V, Exp, Actual]
  )
).
-define(ERR_NOT_DEF(Name), ?FMT("variable ~s is not defined", [Name])).
-define(
  ERR_NOT_DEF(Name, Module),
  ?FMT("variable ~s is not defined in module ~s", [Name, Module])
).
-define(
  ERR_NOT_DEF_TYPE(Con),
  ?FMT("type ~s is not defined", [utils:unqualify(Con)])
).
-define(
  ERR_NOT_DEF_NATIVE(Module, Name, Arity),
  ?FMT("native function ~s:~s/~p is not defined", [Module, Name, Arity])
).
-define(
  ERR_NOT_DEF_MODULE(Module),
  ?FMT("module ~s is not defined or imported", [Module])
).
-define(
  ERR_TYPE_PARAMS(Con, Exp, Actual),
  ?FMT(
    "type ~s accepts ~p type parameters, but you gave it ~p",
    [utils:unqualify(Con), Exp, Actual]
  )
).
-define(
  ERR_DUP_KEY(Key, Con, Line),
  ?FMT(
    "the key ~s is already used for option ~s on line ~p",
    [Key, utils:unqualify(Con), Line]
  )
).
-define(
  ERR_NOT_EXPORTED(Name, Module),
  ?FMT("variable ~s is not exported from module ~s", [Name, Module])
).


-define(LOC(Node), element(2, Node)).

-endif.
