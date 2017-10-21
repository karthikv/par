-ifndef(COMMON_HRL_).
-define(COMMON_HRL_, 1).

% a component to compile, representing a module and its metadata
-record(comp, {module, ast, deps, path, prg, prg_lines}).

% C - A context record for type inference with the following fields:
%   gnr - the current gnr record that constraints are being added to; see G
%     below
%   gnrs - an array of finalized gnr records that need to be solved
%   env - see Env above
%   types - a Name => NumParams map for types in the env
%   aliases - a Name => {Vs, T} map denoting a type alias between the type
%     given by Name and the type T, parameterized by Vs
%   structs - a Name => {T, SigVs} map for structs in the env
%   enums - a EnumName => {[OptionName], ParamTs, GenOptions} map for enums
%   options - a {Module, Name} => Arity map for options
%   ifaces - a Name => {Fields, FieldTs} map for interfaces in the env
%   impls - a ImplKey => RawT map for implementations of interfaces
%   impl_refs - a Ref => ImplKey map for implementations of interfaces
%   sig_ifaces - a map of V => I for TV names in a sig to ensure consistency
%   fn_refs - a Ref => T mapping for fns
%   inst_refs - a Ref => {T, SubbedVs} mapping of instantiated vars
%   nested_ivs - a {I, V} -> IVs mapping for impls depending on other impls
%   errs - an array of error messages, each of the form {Msg, Loc}
%   num_params - the number of type params for the TV being processed
%   gen_vs - a V => GenTVs mapping, where GenTVs all have base V
%   module - the current module
%   imported - a set containing {Module1, Module2} pairs, meaning Module2 has
%              been imported by Module1
%   pid - the process id of the TV server used to generated fresh TVs
-record(ctx, {
  gnr,
  gnrs = [],
  env = #{},
  types = #{
    "Int" => {false, 0},
    "Float" => {false, 0},
    "Bool" => {false, 0},
    "Atom" => {false, 0},
    "Char" => {false, 0},
    "String" => {false, 0},
    "Ref" => {false, 0},
    "Exception" => {false, 0},
    "Test" => {false, 0},
    "Assertion" => {false, 0},
    "List" => {false, 1},
    "Set" => {false, 1},
    "Map" => {false, 2},

    % ifaces
    "Num" => {true, 0},
    "Ord" => {true, 0},
    "Concatable" => {true, 0},
    "Separable" => {true, 0}
  },
  aliases = #{},
  structs = #{},
  enums = #{},
  options = #{},
  ifaces = #{},
  impls = #{
    "Num" => #{},
    "Ord" => #{},
    "Concatable" => #{},
    "Separable" => #{}
  },
  impl_refs = #{},
  sig_vs = #{},
  fn_refs = #{},
  inst_refs,
  nested_ivs,
  num_params,
  errs = [],
  gen_vs = #{},
  module,
  imported = gb_sets:new(),
  pid
}).

% options while performing substitution on a type
-record(sub_opts, {subs, aliases = #{}, for_err = false}).

-define(FMT(Str), lists:flatten(io_lib:format(Str, []))).
-define(FMT(Str, Args), lists:flatten(io_lib:format(Str, Args))).
-define(ERR(Str), io:format(standard_error, Str, [])).
-define(ERR(Str, Args), io:format(standard_error, Str, Args)).

-define(FROM_GLOBAL_DEF(Name), ?FMT("global definition of ~s", [Name])).
-define(FROM_GLOBAL_SIG(Name), ?FMT("global type signature of ~s", [Name])).
-define(FROM_EXPR_SIG, "expression type signature").
-define(FROM_EXPR_SIG_RESULT, "result of expression type signature").
-define(FROM_ENUM_CTOR, "enum constructor").
-define(FROM_STRUCT_CTOR, "struct constructor").
-define(FROM_LIST_ELEM, "element in list literal").
-define(FROM_LIST_TAIL, "list tail").
-define(FROM_MAP_KEY, "key in map literal").
-define(FROM_MAP_VALUE, "value in map literal").
-define(FROM_RECORD_UPDATE, "updating record").
-define(
  FROM_RECORD_CREATE(Con),
  ?FMT("creating record ~s", [utils:unqualify(Con)])
).
-define(FROM_FIELD_DEF(Name), ?FMT("definition of field ~s", [Name])).
-define(FROM_FIELD_ACCESS(Name), ?FMT("accessing field ~s", [Name])).
-define(FROM_APP, "function call").
-define(FROM_IF_COND, "if condition").
-define(FROM_THEN_BODY, "if then body").
-define(FROM_ELSE_BODY, "else body").
-define(FROM_LET, "let pattern").
-define(FROM_IF_LET_PATTERN, "if-let pattern").
-define(FROM_MATCH_PATTERN, "match pattern").
-define(FROM_MATCH_BODY, "match body").
-define(FROM_UNARY_OP(Op), ?FMT("unary ~p operator", [Op])).
-define(FROM_OP_LHS(Op), ?FMT("left-hand side of ~p operator", [Op])).
-define(FROM_OP_RHS(Op), ?FMT("right-hand side of ~p operator", [Op])).
-define(FROM_OP_RESULT(Op), ?FMT("result of ~p operation", [Op])).
-define(FROM_VAR(Name), ?FMT("variable ~p", [Name])).
-define(FROM_IMPL_TYPE, "impl type").
-define(FROM_PARENT_IFACES, "satisfying parent interfaces").


-define(ERR_REDEF(Name), ?FMT("~s is already defined", [Name])).
-define(
  ERR_REDEF_TYPE(Con),
  ?FMT("~s is already defined as a type", [utils:unqualify(Con)])
).
-define(
  ERR_REDEF_BUILTIN_TYPE(Con),
  ?FMT("~s is already defined as a builtin type", [utils:unqualify(Con)])
).
-define(
  ERR_REDEF_IFACE(Con),
  ?FMT("~s is already defined as an interface", [utils:unqualify(Con)])
).
-define(
  ERR_REDEF_BUILTIN_IFACE(Con),
  ?FMT("~s is already defined as a builtin interface", [utils:unqualify(Con)])
).
-define(
  ERR_REDEF_TV(Con),
  ?FMT("Type variable ~s is already defined", [utils:unqualify(Con)]
)).
-define(
  ERR_REDEF_MODULE(Module),
  ?FMT("Module ~s is already defined", [Module])
).
-define(
  ERR_SIG_NO_DEF(Name),
  ?FMT("Expected ~s to be defined after its signature", [Name])
).
-define(ERR_DUP_FIELD(Name), ?FMT("Duplicate field ~s in this record", [Name])).
-define(
  ERR_DUP_FIELD_IMPL(Name),
  ?FMT("Duplicate field ~s in this implementation", [Name])
).
-define(
  ERR_DUP_FIELD_PARENT(Name, ParentCon),
  ?FMT(
    "Duplicate field ~s that already exists in parent interface ~s",
    [Name, utils:unqualify(ParentCon)]
  )
).
-define(
  ERR_EXTRA_FIELD_IMPL(Name, Con),
  ?FMT(
    "Field ~s isn't in interface ~s, so it shouldn't be implemented",
    [Name, utils:unqualify(Con)]
  )
).
-define(
  ERR_MISSING_FIELD_IMPL(Name, Con),
  ?FMT(
    "Missing field ~s in implementation of interface ~s",
    [Name, utils:unqualify(Con)]
  )
).
-define(
  ERR_TV_SCOPE(V),
  "Type variable ~s isn't in scope; you must specify a concrete type."
).
-define(
  ERR_TV_SCOPE(V, Con),
  ?FMT(
    "Type variable ~s isn't in scope; it must be defined as a parameter to "
    "type ~s",
    [V, utils:unqualify(Con)]
  )
).
-define(
  ERR_TV_IFACE(V, ExpIs, Is),
  ?FMT(
    "Type variable ~s was previously ~s, but is now ~s; the interfaces must "
    "must be consistent",
    [V, utils:pretty({tv, V, ExpIs, false}), utils:pretty({tv, V, Is, false})]
  )
).
-define(
  ERR_TV_NUM_PARAMS(V, ExpNum, Num),
  ?FMT(
    "Type variable ~s was previously given ~p type parameters, but now has ~p; "
    "the two must be consistent",
    [V, ExpNum, Num]
  )
).
-define(ERR_NOT_DEF(Name), ?FMT("~s is not defined", [Name])).
-define(
  ERR_NOT_DEF(Name, Module),
  ?FMT("~s is not defined in module ~s", [Name, Module])
).
-define(
  ERR_NOT_DEF_TYPE(Con),
  ?FMT("Type ~s is not defined", [utils:unqualify(Con)])
).
-define(
  ERR_NOT_DEF_TYPE(Con, Module),
  ?FMT("Type ~s is not defined in module ~s", [utils:unqualify(Con), Module])
).
-define(
  ERR_NOT_DEF_IFACE(Con),
  ?FMT("Interface ~s is not defined", [utils:unqualify(Con)])
).
-define(
  ERR_NOT_DEF_NATIVE(Module, Name, Arity),
  ?FMT("Native function ~s:~s/~p is not defined", [Module, Name, Arity])
).
-define(
  ERR_NOT_DEF_MODULE(Module),
  ?FMT("Module ~s is not defined or imported", [Module])
).
-define(
  ERR_TYPE_PARAMS(Con, Exp, Actual),
  ?FMT(
    "Type ~s accepts ~p type parameters, but you gave it ~p",
    [utils:unqualify(Con), Exp, Actual]
  )
).
-define(
  ERR_DUP_KEY(Key, Con, Loc),
  ?FMT(
    "The key ~s is already used for option ~s on line ~p, column ~p",
    [Key, utils:unqualify(Con), ?START_LINE(Loc), ?START_COL(Loc)]
  )
).
-define(
  ERR_NOT_EXPORTED(Name, Module),
  ?FMT("~s is not exported from module ~s", [Name, Module])
).
-define(
  ERR_DUP_IMPORT(Name, Loc),
  ?FMT(
    "~s is already imported on line ~p, column ~p",
    [Name, ?START_LINE(Loc), ?START_COL(Loc)]
  )
).
-define(
  ERR_TYPE_NOT_IFACE(Con),
  ?FMT("~s is a type, not an interface", [utils:unqualify(Con)])
).
-define(
  ERR_IFACE_NOT_TYPE(Con),
  ?FMT("~s is an interface, not a type", [utils:unqualify(Con)])
).
-define(
  ERR_DUP_IMPL(Con, Key, PrettyT),
  ?FMT(
    "Can only have one implementation that resembles a ~s for interface ~s; "
    "an implementation already exists for type ~s",
    [Key, utils:unqualify(Con), PrettyT]
  )
).
-define(
  ERR_IFACE_TYPE(Name),
  ?FMT(
    "The type of interface field ~s must be a function that has T in its "
    "type signature",
    [Name]
  )
).
-define(
  ERR_MUST_SOLVE_ARG(PrettyTV, PrettyArgT),
  ?FMT(
    "Ambiguous argument of type ~s. I need to know the concrete type of the "
    "type variable ~s so I can ensure its interfaces are satisifed. Please "
    "provide a type signature for this argument that specifies the concrete "
    "type.",
    [PrettyArgT, PrettyTV]
  )
).
-define(
  ERR_MUST_SOLVE_RETURN(PrettyTV, PrettyReturnT),
  ?FMT(
    "Ambiguous return type ~s. The function that needs to be called here "
    "depends on what the return type is. Specifically, I need to know the "
    "concrete type of the type variable ~s. Please provide a type signature "
    "for the return value that specifies the concrete type.",
    [PrettyReturnT, PrettyTV]
  )
).
-define(
  ERR_IMPL_TYPE(Con),
  ?FMT(
    "The interface ~s must be implemented for a type constructor. Please "
    "specify a type constructor as a single, capitalized name, like List or "
    "Set.",
    [utils:unqualify(Con)]
  )
).
-define(
  ERR_CYCLE(Con, ParentCon),
  ?FMT(
    "Making ~s extend ~s would cause a cycle. ~s is already an ancestor "
    "interface of ~s.", [
      utils:unqualify(Con),
      utils:unqualify(ParentCon),
      utils:unqualify(Con),
      utils:unqualify(ParentCon)
    ]
  )
).
-define(
  ERR_MATCH_STRUCT,
  "Pattern matching against structs is not supported."
).
-define(
  ERR_OPTION_ARITY(Con, ExpArity, Arity),
  ?FMT(
    "In a pattern, ~s must be given all ~p arguments, but it's only given ~p.",
    [Con, ExpArity, Arity]
  )
).


-define(LOC(Node), element(2, Node)).
-define(START_LINE(Loc), maps:get(start_line, Loc)).
-define(START_COL(Loc), maps:get(start_col, Loc)).

-endif.
