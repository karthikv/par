-ifndef(COMMON_HRL_).
-define(COMMON_HRL_, 1).

-define(MODULE_PREFIX, "Par.").
-define(BUILTIN_LOC, builtin).

-define(
  BUILTIN_TYPE(IsIface, NumParams),
  #type_binding{
    is_iface = IsIface,
    num_params = NumParams,
    loc = ?BUILTIN_LOC
  }
).

% a component to compile, representing a module and its metadata
-record(comp, {module, ast, deps, path, prg, prg_lines}).

% a variable binding in the global or local env
-record(binding, {
  tv,
  id,
  exported = false,
  arity,
  inst,
  loc,
  soft = false,
  modules
}).

% a global type binding; types are exported by default
-record(type_binding, {
  is_iface,
  num_params,
  exported = true,
  loc,
  soft = false,
  modules
}).

% C - A context record for type inference with the following fields:
%   gnr - the current gnr record that constraints are being added to; see G
%     below
%   gnrs - an array of finalized gnr records that need to be solved
%   env - a Name => binding record mapping of bindings in the environment
%   exports - a Module => set of names mapping of exported identifiers (incl.
%     types) in a given module
%   types - a Name => type binding record mapping of types in the env
%   aliases - a Name => {Vs, T} map denoting a type alias between the type
%     given by Name and the type T, parameterized by Vs
%   structs - a Name => {T, SigVs} map for structs in the env
%   enums - a EnumName => {[OptionName], ParamTs, GenOptions} map for enums
%   ifaces - a Name => {Fields, FieldTs} map for interfaces in the env
%   impls - a ImplKey => RawT map for implementations of interfaces
%   impl_refs - a Ref => ImplKey map for implementations of interfaces
%   sig_vs - a map of V => I for TV names in a sig to ensure consistency
%   fn_refs - a Ref => T mapping for fns
%   inst_refs - a Ref => {T, SubbedVs} mapping of instantiated vars
%   nested_ivs - a {I, V} -> IVs mapping for impls depending on other impls
%   num_params - the number of type params for the TV being processed
%   errs - an array of error messages, each of the form {Msg, Loc}
%   gen_vs - a V => GenTVs mapping, where GenTVs all have base V
%   record_refs - a Ref => T mapping of types for anonymous records
%   module - the current module
%   imported - a set containing {Module1, Module2} pairs, meaning Module2 has
%              been imported by Module1
%   pid - the process id of the TV server used to generated fresh TVs
-record(ctx, {
  gnr,
  gnrs = [],
  g_env = #{},
  l_env = #{},
  exports = #{},
  types = #{
    "()" => ?BUILTIN_TYPE(false, 0),
    "Int" => ?BUILTIN_TYPE(false, 0),
    "Float" => ?BUILTIN_TYPE(false, 0),
    "Bool" => ?BUILTIN_TYPE(false, 0),
    "Atom" => ?BUILTIN_TYPE(false, 0),
    "Char" => ?BUILTIN_TYPE(false, 0),
    "String" => ?BUILTIN_TYPE(false, 0),
    "Ref" => ?BUILTIN_TYPE(false, 0),
    "Exception" => ?BUILTIN_TYPE(false, 0),
    "Test" => ?BUILTIN_TYPE(false, 0),
    "Assertion" => ?BUILTIN_TYPE(false, 0),
    "Native" => ?BUILTIN_TYPE(false, 0),
    "List" => ?BUILTIN_TYPE(false, 1),
    "Set" => ?BUILTIN_TYPE(false, 1),
    "Map" => ?BUILTIN_TYPE(false, 2),

    % ifaces
    "Num" => ?BUILTIN_TYPE(true, 0),
    "Ord" => ?BUILTIN_TYPE(true, 0)
  },
  aliases = #{},
  structs = #{},
  enums = #{},
  ifaces = #{},
  impls = #{
    "Num" => #{},
    "Ord" => #{}
  },
  impl_refs = #{},
  sig_vs = #{},
  fn_refs = #{},
  inst_refs,
  nested_ivs,
  num_params,
  errs = [],
  gen_vs = #{},
  record_refs = #{},
  module,
  imported = ordsets:new(),
  pid
}).

% options while performing substitution on a type
-record(sub_opts, {
  subs,
  aliases = #{},
  unalias = false,
  for_err = false,
  shallow = false
}).

-define(FMT(Str), lists:flatten(io_lib:format(Str, []))).
-define(FMT(Str, Args), lists:flatten(io_lib:format(Str, Args))).
-define(ERR(Str), io:format(standard_error, Str, [])).
-define(ERR(Str, Args), io:format(standard_error, Str, Args)).

-define(FROM_GLOBAL_DEF(Name), ?FMT("global definition of ~s", [Name])).
-define(FROM_GLOBAL_SIG(Name), ?FMT("global type signature of ~s", [Name])).
-define(
  FROM_IFACE_SIG(Con),
  ?FMT("satisfying interface ~s", [utils:unqualify(Con)])
).
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
-define(FROM_MATCH_HEAD, "match head").
-define(FROM_MATCH_PATTERN, "match pattern").
-define(FROM_MATCH_BODY, "match body").
-define(FROM_UNARY_OP(Op), ?FMT("unary ~p operator", [Op])).
-define(FROM_CONCAT, "'++' operator").
-define(FROM_OP_LHS(Op), ?FMT("left-hand side of ~p operator", [Op])).
-define(FROM_OP_RHS(Op), ?FMT("right-hand side of ~p operator", [Op])).
-define(FROM_OP_RESULT(Op), ?FMT("result of ~p operation", [Op])).
-define(FROM_VAR(Name), ?FMT("variable ~p", [Name])).
-define(FROM_IMPL_TYPE, "impl type").
-define(FROM_PARENT_IFACES, "satisfying parent interfaces").


-define(MISMATCH_PREFIX, "Mismatched types ").
-define(ERR_TYPE_MISMATCH(T1, T2, From), [
  ?MISMATCH_PREFIX, T1, " and ", T2, " from ", From
]).
-define(ERR_RIGID_CON(TV), [
  TV, " is a rigid type variable, meaning it represents some type, but you "
  "don't know what specific type that is. You cannot assume ", TV,
  " is any particular concrete type. This error may occur when there's a "
  "function type signature that says a parameter can be any type (e.g. even "
  ": A -> Bool), but your function body assumes that parameter is some "
  "specific type (e.g. even(x) = x % 2 == 0). In this example case, the "
  "signature should be even : Int -> Bool"
]).
-define(ERR_RIGID_TV(RigidTV, TV), [
  "The type variable ", TV, " contains at least one interface that's not in ",
  RigidTV, ". Because ", RigidTV, " is a rigid type variable specified by a "
  "type signature, it cannot have any additional interfaces"
]).
-define(ERR_RIGID_BOUND(RigidTV, BoundTV), [
  BoundTV, " is a type variable that comes from an argument of an enclosing "
  "function. This means ", BoundTV, " is a specific concrete type that's "
  "passed in. But ", RigidTV, " is a rigid type variable that represents "
  "many types (i.e. it is polymorphic). Hence, I cannot match ", BoundTV,
  " and any type that contains ", RigidTV
]).
-define(ERR_RIGID_RIGID(TV1, TV2), [
  TV1, " and ", TV2, " are rigid type variables, meaning they represent two "
  "types, but you don't know what those specific types are. You cannot "
  "assume ", TV1, " and ", TV2, " are the same type"
]).
-define(ERR_ARITY(Given, Exp), ?FMT(
  "You provided ~p argument(s), but this function needs ~p argument(s)",
  [Given, Exp]
)).
-define(ERR_HOLE(T), [
  "Unexpected '_'. I'm looking for a value of type ", T, " here. '_' can be "
  "used in a pattern if you don't need a reference to the value, as in let "
  "[h | _] = foo(). It may also be used to partially apply a function, such "
  "as in max(_, 3)"
]).


-define(ERR_REDEF(Name, Loc), [
  utils:unqualify(Name), " was already defined at", Loc,
  "You can't redefine it here"
]).
-define(ERR_REDEF_BUILTIN(Name), ?FMT(
  "~s is already defined as a builtin",
  [utils:unqualify(Name)]
)).
-define(ERR_REDEF_BUILTIN_TYPE(Name), ?FMT(
  "~s is already defined as a builtin type",
  [utils:unqualify(Name)]
)).
-define(ERR_REDEF_BUILTIN_IFACE(Name), ?FMT(
  "~s is already defined as a builtin interface",
  [utils:unqualify(Name)]
)).
-define(ERR_REDEF_TV(V), ?FMT(
  "Type variable ~s is already defined",
  [V]
)).
-define(ERR_REDEF_MODULE(Module), ?FMT(
  "Module ~s is already defined", [Module]
)).
-define(ERR_SIG_NO_DEF(Name), ?FMT(
  "Expected ~s to be defined after its signature",
  [Name]
)).
-define(ERR_DUP_FIELD(Name), ?FMT(
  "Duplicate field ~s in this record",
  [Name]
)).
-define(ERR_DUP_FIELD_IMPL(Name), ?FMT(
  "Duplicate field ~s in this implementation",
  [Name]
)).
-define(ERR_DUP_FIELD_PARENT(Name, ParentCon), ?FMT(
  "Duplicate field ~s that already exists in parent interface ~s",
  [Name, utils:unqualify(ParentCon)]
)).
-define(ERR_EXTRA_FIELD_IMPL(Name, Con), ?FMT(
  "Field ~s isn't in interface ~s, so it shouldn't be implemented",
  [Name, utils:unqualify(Con)]
)).
-define(ERR_MISSING_FIELD_IMPL(Name, Con), ?FMT(
  "Missing field ~s in implementation of interface ~s",
  [Name, utils:unqualify(Con)]
)).
-define(ERR_TV_SCOPE(V), ?FMT(
  "Type variable ~s isn't in scope; you must specify a concrete type",
  [V]
)).
-define(ERR_TV_SCOPE(V, Con), ?FMT(
  "Type variable ~s isn't in scope; it must be defined as a parameter to "
  "type ~s",
  [V, utils:unqualify(Con)]
)).
-define(ERR_TV_IFACE(V, ExpIs, Is), ?FMT(
  "Type variable ~s was previously ~s, but is now ~s; the interfaces must "
  "must be consistent",
  [V, utils:pretty({tv, V, ExpIs, false}), utils:pretty({tv, V, Is, false})]
)).
-define(ERR_TV_NUM_PARAMS(V, ExpNum, Num), ?FMT(
  "Type variable ~s was previously given ~p type parameters, but now has ~p; "
  "the two must be consistent",
  [V, ExpNum, Num]
)).
-define(ERR_NOT_DEF(Name), ?FMT("~s is not defined", [Name])).
-define(ERR_NOT_DEF(Name, Module), ?FMT(
  "~s is not defined in module ~s",
  [Name, Module]
)).
-define(ERR_NOT_DEF_TYPE(Con), ?FMT(
  "Type ~s is not defined",
  [utils:unqualify(Con)]
)).
-define(ERR_NOT_DEF_TYPE(Con, Module), ?FMT(
  "Type ~s is not defined in module ~s",
  [utils:unqualify(Con), Module]
)).
-define(ERR_NOT_DEF_IFACE(Con), ?FMT(
  "Interface ~s is not defined",
  [utils:unqualify(Con)]
)).
-define(ERR_NOT_DEF_NATIVE(Module, Name, Arity), ?FMT(
  "Native function ~s:~s/~p is not defined",
  [Module, Name, Arity]
)).
-define(ERR_NOT_DEF_MODULE(Module), ?FMT(
  "Module ~s is not defined or imported",
  [Module]
)).
-define(ERR_TYPE_PARAMS(Con, Exp, Given), ?FMT(
  "Type ~s accepts ~p type parameters, but you gave it ~p",
  [utils:unqualify(Con), Exp, Given]
)).
-define(ERR_DUP_KEY(Key, Con, Loc), [
  "The key ", atom_to_list(Key), " was already used for option ",
  utils:unqualify(Con), " at", Loc, "You can't reuse it here"
]).
-define(ERR_NOT_EXPORTED(Name, Module), ?FMT(
  "~s is not exported from module ~s",
  [Name, Module]
)).
-define(ERR_DUP_IMPORT(Name, Loc), [
  Name, " was already imported at", Loc, "You can't import it again here"
]).
-define(ERR_TYPE_NOT_IFACE(Con), ?FMT(
  "~s is a type, not an interface",
  [utils:unqualify(Con)]
)).
-define(ERR_IFACE_NOT_TYPE(Con), ?FMT(
  "~s is an interface, not a type",
  [utils:unqualify(Con)]
)).
% PrettyT is not normalized because it's exactly what the user entered.
-define(ERR_DUP_IMPL(Con, Key, PrettyT), ?FMT(
  "Can only have one implementation that resembles a ~s for interface ~s; "
  "an implementation already exists for type ~s",
  [Key, utils:unqualify(Con), PrettyT]
)).
-define(ERR_IFACE_TYPE(Name), ?FMT(
  "The type of interface field ~s must be a function that has T in its "
  "type signature",
  [Name]
)).
-define(ERR_MUST_SOLVE_ARG(ArgT, TV), [
  "Ambiguous argument of type ", ArgT, ". I need to know the concrete type "
  "of the type variable ", TV, " so I can ensure its interfaces are satisifed. "
  "Please provide a type signature for this argument that specifies the "
  "concrete type"
]).
-define(ERR_MUST_SOLVE_RETURN(ReturnT, TV), [
  "Ambiguous return type ", ReturnT, ". The function that needs to be called "
  "here depends on what the return type is. Specifically, I need to know the "
  "concrete type of the type variable ", TV, ". Please provide a type "
  "signature for the return value that specifies the concrete type"
]).
-define(ERR_IMPL_TYPE(Con), ?FMT(
  "The interface ~s must be implemented for a type constructor. Please "
  "specify a type constructor as a single, capitalized name, like List or "
  "Set",
  [utils:unqualify(Con)]
)).
-define(ERR_CYCLE(Con, ParentCon), ?FMT(
  "Making ~s extend ~s would cause a cycle. ~s is already an ancestor "
  "interface of ~s", [
    utils:unqualify(Con),
    utils:unqualify(ParentCon),
    utils:unqualify(Con),
    utils:unqualify(ParentCon)
  ]
)).
-define(ERR_MATCH_STRUCT, "Pattern matching against structs is not supported").
-define(ERR_AMBIG(Name, Modules), [
  utils:unqualify(Name), " is ambiguous, since you've directly imported it "
  "from multiple modules. Do you mean ",
  lists:join(" or ", [[M, ".", utils:unqualify(Name)] || M <- Modules]),
  "? Please use the fully qualified name, or don't directly import the "
  "conflicting names"
]).
-define(ERR_CANT_IMPL(Con), [
  "You can't implement the builtin interface ", Con
]).

-define(LOC(Node), element(2, Node)).
-define(START_LINE(Loc), maps:get(start_line, Loc)).
-define(START_COL(Loc), maps:get(start_col, Loc)).

-endif.
