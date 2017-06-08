-ifndef(ERRORS_HRL_).
-define(ERRORS_HRL_, 1).

-define(FMT(Str, Args), lists:flatten(io_lib:format(Str, Args))).

-define(FROM_GLOBAL_DEF, "global definition").
-define(FROM_GLOBAL_SIG, "global type signature").
-define(FROM_EXPR_SIG, "expression type signature").
-define(FROM_ENUM_CTOR, "enum constructor").
-define(FROM_STRUCT_CTOR, "struct constructor").
-define(FROM_LIST_ELEM, "element in list literal").
-define(FROM_LIST_TAIL, "list tail pattern").
-define(FROM_MAP_KEY, "key in map literal").
-define(FROM_MAP_VALUE, "value in map literal").
-define(FROM_RECORD_UPDATE, "updating record").
-define(FROM_RECORD_CREATE(Name), ?FMT("creating ~s record", [Name])).
-define(FROM_FIELD_ACCESS(Name), ?FMT("accessing ~s field", [Name])).
-define(FROM_APP, "function call").
-define(FROM_IF_COND, "if condition").
-define(FROM_IF_BODY, "if/else body").
-define(FROM_LET, "let pattern").
-define(FROM_IF_LET_PATTERN, "if-let pattern").
-define(FROM_IF_LET_BODY, "if-let/else body").
-define(FROM_MATCH_PATTERN, "match pattern").
-define(FROM_MATCH_BODY, "match body").
-define(FROM_OP(Op), ?FMT("~p operator", [Op])).

-endif.
