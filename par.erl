-module(par).
-export([reload/1, infer_prg/1, subs/2, fvs/1, pretty/1]).

% Naming conventions:
%
% TV - a type variable, represented as a 4-tuple {tv, V, I, Cat}:
%   V - the variable name
%   I - the interface (typeclass) constraining the type variable
%   Cat - the category of type variable (any or all)
%
% T - a type, represented as a tuple:
%   {con, C} - a concrete type C; e.g. Int
%   {gen, G, T} - a generic type G<T>; e.g. List<String>
%   {tuple, L, R} - a tuple type (L, R); e.g. (Int, Bool)
%   {lam, X, Y} - a lambda type X -> Y; e.g. Int -> Bool
%   TV - see explanation above
%
% fresh - a function that generates a new TV.
% fvs - a function that computes the set of free TV names in an expression.
% Scheme - a tuple {GVs, T} that represents a T generalized across GVs, a set of
%          TV names.
% Env - a Name => T mapping of bindings in the environment.

% C - A context record for type inference with the following fields:
%   gnr - the current gnr record that constraints are being added to; see G
%         below
%   gnrs - an array of finalized gnr records that need to be solved
%   env - see Env above
%   types - a Name => TypeInfo mapping of types in the environment
%   in_pattern - true if within a pattern, false otherwise
%   pattern_env - new variables introduced as part of a pattern
%   pid - the process id of the TV server used to generated fresh TVs
-record(ctx, {gnr, gnrs, env, types, in_pattern, pattern_env, pid}).

% S - a solver record used to unify types and solve constraints
%   subs - the substitutions made to unify types
%   errs - any constraints that couldn't be unified
%   schemes - the schemes of env variables that have been solved for and
%             generalized
%   rigid_vs - the set of TV names in the environment
%   pid - the process id of the TV server used to generated fresh TVs
-record(solver, {subs, errs, schemes, rigid_vs, pid}).

% G - a gnr record that represents a set of constraints to solve before
%     generalizing a type variable:
%   v - the TV name to generalize
%   env - see Env above
%   csts - an array of constraints to solve before generalizing
%   deps - an array of TV names corresponding to gnr records that need to
%          solved before this record or, in the case of (mutual) recursion,
%          simultaneously with this record
%   index / low_link / on_stack - bookkeeping for Tarjan's strongly connected
%                                 components algorithm; see T below and [1]
-record(gnr, {id, vs, env, csts, deps, index, low_link, on_stack}).

% T - A tarjan record that's used to apply Tarjan's strongly connected
%     components algorithm. This is necessary to solve constraints in the proper
%     order so as to respect dependencies.
%   map - a V => gnr record mapping so you can find the appropriate node given
%         the TV name
%   stack / next_index - bookkeeping for Tarjan's algorithm; see [1]
%   solver - the solver record used for unification; see S below
%
% [1] https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm
-record(tarjan, {stack, map, next_index, solver}).

-ifdef(release).
  -define(LOG(Prefix, Value), true).
-else.
  -define(
    LOG(Prefix, Value),
    io:format("~n(~p:~p) ~s:~n~p~n", [?MODULE, ?LINE, Prefix, Value])
  ).
-endif.

% TODO:
% - TODOs in code (non-unification error cases)
% - Error messages
% - Imports
% - Typeclasses + generics w/o concrete types (HKTs)
% - Updating and accessing a struct
% - else precedence
% - Concurrency
% - Pattern matching
% - Exceptions
% - Code generation
% - Update naming conventions
%
% - + instead of ++ and - instead of --?
% - Reverse csts before solving for better error messages?
% - Make true/false capitalized?
% - Syntax for lambda with no arg?
% - Operation: nth element of tuple?
% - Unit as valid expression?
% - Force all block expressions except last to be type ()?

reload(true) ->
  code:purge(lexer),
  {ok, _} = leex:file(lexer),
  {ok, _} = compile:file(lexer),
  code:load_file(lexer),

  code:purge(parser),
  {ok, _} = yecc:file(parser),
  {ok, _} = compile:file(parser),
  code:load_file(parser),

  reload(false);

reload(false) ->
  tv_server:reload(),

  code:purge(?MODULE),
  {ok, _} = compile:file(?MODULE),
  code:load_file(?MODULE).

infer_prg(Prg) ->
  {ok, Tokens, _} = lexer:string(Prg),
  {ok, Ast} = parser:parse(Tokens),
  ?LOG("AST", Ast),
  {ok, Pid} = tv_server:start_link(),

  C = #ctx{
    gnr=undefined,
    gnrs=[],
    env=#{},
    types=#{},
    in_pattern=false,
    pattern_env=undefined,
    pid=Pid
  },
  C1 = lists:foldl(fun(Node, FoldC) ->
    case Node of
      {global, {var, _, Name}, _} ->
        % TODO: what if name already exists?
        {TV, ID} = tv_server:fresh_gnr_id(FoldC#ctx.pid),
        add_env(Name, {add_dep, TV, ID}, FoldC);

      % TODO: register valid type for each enum/struct

      _ -> FoldC
    end
  end, C, Ast),

  C2 = lists:foldl(fun(Node, FoldC) ->
    case Node of
      {N, _, _} when N == enum; N == struct ->
        {_, FoldC1} = infer(Node, FoldC),
        FoldC1;

      _ -> FoldC
    end
  end, C1, Ast),

  {_, _, C3} = lists:foldl(fun(Node, {ExpName, SigT, FoldC}) ->
    if
      % TODO: handle error
      ExpName /= none -> {global, {var, _, ExpName}, _} = Node;
      true -> none
    end,

    case Node of
      {global, {var, _, Name}, Expr} ->
        #{Name := {add_dep, TV, ID}} = FoldC#ctx.env,
        % for generalization, use env that doesn't contain any globals
        % TODO: should anything be in this map?
        FoldC1 = new_gnr(TV, ID, FoldC),
        {T, FoldC2} = infer(Expr, FoldC1),

        Csts = if
          SigT == none -> [{TV, T}];
          true -> [{TV, T}, {TV, SigT}]
        end,
        FoldC3 = add_csts(Csts, FoldC2),

        {none, none, finish_gnr(FoldC3, FoldC#ctx.gnr)};

      {sig, {var, _, Name}, _} ->
        {T, FoldC1} = infer(Node, FoldC),
        {Name, T, FoldC1};

      % we've already processed enums/structs
      _ -> {ExpName, SigT, FoldC}
    end
  end, {none, none, C2}, Ast),

  S = #solver{subs=#{}, errs=[], schemes=#{}, pid=Pid},
  Result = case solve(C3#ctx.gnrs, S) of
    {ok, Subs} ->
      SubbedEnv = maps:map(fun(_, Value) ->
        EnvTV = case Value of
          {no_dep, TV} -> TV;
          {add_dep, TV, _} -> TV
        end,
        subs(EnvTV, Subs)
      end, C3#ctx.env),
      {ok, SubbedEnv, Ast};
    {errors, Errs} -> {errors, Errs}
  end,

  ok = tv_server:stop(Pid),
  Result.

infer({fn, Args, Expr}, C) ->
  {ArgTsRev, C1} = lists:foldl(fun({var, _, ArgName}, {Ts, FoldC}) ->
    ArgTV = tv_server:fresh(FoldC#ctx.pid),
    {[ArgTV | Ts], add_env(ArgName, {no_dep, ArgTV}, FoldC)}
  end, {[], C}, Args),

  {ReturnT, C2} = infer(Expr, C1),
  T = if
    length(Args) == 0 -> {lam, none, ReturnT};
    true -> lists:foldl(fun(ArgT, LastT) ->
      {lam, ArgT, LastT}
    end, ReturnT, ArgTsRev)
  end,

  % restore original env
  {T, C2#ctx{env=C#ctx.env}};

infer({sig, _, Sig}, C) ->
  {SigT, C1} = infer(Sig, C),
  {norm_sig_type(SigT, C#ctx.pid), C1};

infer({expr_sig, Expr, Sig}, C) ->
  G = C#ctx.gnr,
  {TV, ID} = tv_server:fresh_gnr_id(C#ctx.pid),

  {ExprT, C1} = infer(Expr, new_gnr(TV, ID, C)),
  {SigT, C2} = infer(Sig, C1),
  NormSigT = norm_sig_type(SigT, C2#ctx.pid),

  C3 = add_csts([{TV, ExprT}, {TV, NormSigT}], C2),
  {{inst, TV}, finish_gnr(C3, G#gnr{deps=[ID | G#gnr.deps]})};

infer({lam_te, ArgTE, ReturnTE}, C) ->
  {ArgT, C1} = infer(ArgTE, C),
  {ReturnT, C2} = infer(ReturnTE, C1),
  {{lam, ArgT, ReturnT}, C2};
infer({tuple_te, LeftTE, RightTE}, C) ->
  {LeftT, C1} = infer(LeftTE, C),
  {RightT, C2} = infer(RightTE, C1),
  {{tuple, LeftT, RightT}, C2};
infer({iface_te, TVToken, ConToken}, C) ->
  {{tv, V, none, Cat}, C1} = infer(TVToken, C),
  {{con, I}, C2} = infer(ConToken, C1),
  {{tv, V, I, Cat}, C2};
infer({gen_te, ConToken, ParamTE}, C) ->
  {{con, T}, C1} = infer(ConToken, C),
  {ParamT, C2} = infer(ParamTE, C1),
  {{gen, T, ParamT}, C2};
infer({tv_token, _, Name}, C) ->
  % This TV should be in category all, but because it's renamed in
  % norm_sig_type, it's reset to category any. Hence, we don't set category all
  % here. Rather, after renaming in norm_sig_type, we change to category all.
  {{tv, Name, none, any}, C};
% TODO: ensure these types are valid except when creating a new type
infer({con_token, _, Name}, C) -> {{con, list_to_atom(Name)}, C};

infer({enum, EnumTE, OptionTEs}, C) ->
  {T, C1} = infer(EnumTE, C),
  C2 = lists:foldl(fun({option, {con_token, _, Name}, ArgTEs}, FoldC) ->
    {ArgTsRev, FoldC1} = lists:foldl(fun(ArgTE, {Ts, InnerC}) ->
      {ArgT, InnerC1} = infer(ArgTE, InnerC),
      {[ArgT | Ts], InnerC1}
    end, {[], FoldC}, ArgTEs),

    OptionT = lists:foldl(fun(ArgT, LastT) ->
      {lam, ArgT, LastT}
    end, T, ArgTsRev),
    NormOptionT = norm_sig_type(OptionT, C#ctx.pid),

    % TODO: what if name already exists?
    {TV, ID} = tv_server:fresh_gnr_id(C#ctx.pid),
    FoldC2 = add_csts({TV, NormOptionT}, new_gnr(TV, ID, FoldC1)),
    add_env(Name, {add_dep, TV, ID}, finish_gnr(FoldC2, FoldC1#ctx.gnr))
  end, C1, OptionTEs),

  {T, C2};

infer({struct, StructTE, FieldTEs}, C) ->
  {T, C1} = infer(StructTE, C),
  {ArgTsRev, FieldNamesRev, C2} = lists:foldl(fun(TE, {Ts, Names, FoldC}) ->
    {field, {var, _, Name}, Sig} = TE,
    {FieldT, FoldC1} = infer(Sig, FoldC),
    {[FieldT | Ts], [Name | Names], FoldC1}
  end, {[], [], C1}, FieldTEs),

  FnT = lists:foldl(fun(ArgT, LastT) ->
    {lam, ArgT, LastT}
  end, T, ArgTsRev),
  NormFnT = norm_sig_type(FnT, C2#ctx.pid),

  StructName = case StructTE of
    {con_token, _, Name} -> Name;
    {gen_te, {con_token, _, Name}, _} -> Name
  end,

  % TODO: test recursive struct
  {TV, ID} = tv_server:fresh_gnr_id(C2#ctx.pid),
  C3 = add_env(StructName, {add_dep, TV, ID}, C2),
  NewTypes = (C3#ctx.types)#{StructName => {struct, FieldNamesRev}},

  C4 = new_gnr(TV, ID, C3#ctx{types=NewTypes}),
  C5 = finish_gnr(add_csts({TV, NormFnT}, C4), C3#ctx.gnr),
  {TV, C5};

infer(none, C) -> {none, C};
infer({int, _, _}, C) -> {tv_server:fresh('Num', C#ctx.pid), C};
infer({float, _, _}, C) -> {{con, 'Float'}, C};
infer({bool, _, _}, C) -> {{con, 'Bool'}, C};
infer({str, _, _}, C) -> {{con, 'String'}, C};
infer({atom, _, _}, C) -> {{con, 'Atom'}, C};

infer({list, Elems}, C) ->
  TV = tv_server:fresh(C#ctx.pid),
  {Csts, C1} = lists:foldl(fun(Elem, {FoldCsts, FoldC}) ->
    {ElemT, FoldC1} = infer(Elem, FoldC),
    {[{ElemT, TV} | FoldCsts], FoldC1}
  end, {[], C}, Elems),

  {{gen, 'List', TV}, add_csts(Csts, C1)};

% only occurs when pattern matching to destructure list into head/tail
infer({list, Elems, Rest}, C) ->
  true = C#ctx.in_pattern,
  {T, C1} = infer({list, Elems}, C),
  {RestT, C2} = infer(Rest, C1),
  {T, add_csts({T, RestT}, C2)};

infer({tuple, Left, Right}, C) ->
  {LeftT, C1} = infer(Left, C),
  {RightT, C2} = infer(Right, C1),
  {{tuple, LeftT, RightT}, C2};

infer({map, Pairs}, C) ->
  KeyTV = tv_server:fresh(C#ctx.pid),
  ValueTV = tv_server:fresh(C#ctx.pid),

  {Csts, C1} = lists:foldl(fun({Key, Value}, {FoldCsts, FoldC}) ->
    {KeyT, FoldC1} = infer(Key, FoldC),
    {ValueT, FoldC2} = infer(Value, FoldC1),
    {[{KeyT, KeyTV}, {ValueT, ValueTV} | FoldCsts], FoldC2}
  end, {[], C}, Pairs),

  {{gen, 'Map', {tuple, KeyTV, ValueTV}}, add_csts(Csts, C1)};

infer({var, _, Name}, C) ->
  case C#ctx.in_pattern of
    false -> lookup(Name, C);
    true ->
      PatternEnv = C#ctx.pattern_env,
      case maps:find(Name, PatternEnv) of
        {ok, TV} -> {TV, C};
        error ->
          TV = tv_server:fresh(C#ctx.pid),
          {TV, C#ctx{pattern_env=PatternEnv#{Name => TV}}}
      end
  end;

% only occurs when pattern matching to designate a non-literal variable
infer({var_value, _, Name}, C) -> lookup(Name, C);

% only occurs when pattern matching to designate anything
infer({'_', _}, C) -> {tv_server:fresh(C#ctx.pid), C};

infer({con_var, _, Name}, C) -> lookup(Name, C);

infer({record, ConVar, Inits}, C) ->
  {FnT, C1} = infer(ConVar, C),
  {con_var, _, StructName} = ConVar,
  % TODO: should FieldNames be in the types map or in the env map? Update
  % TypeInfo description in naming conventions after figuring this out
  #{StructName := {struct, FieldNamesRev}} = C1#ctx.types,

  {InitNameTs, C2} = lists:foldl(fun(Init, {NameTs, FoldC}) ->
    {{var, _, Name}, Expr} = Init,
    {T, FoldC1} = infer(Expr, FoldC),
    {[{Name, T} | NameTs], FoldC1}
  end, {[], C1}, Inits),

  TV = tv_server:fresh(C2#ctx.pid),
  T = lists:foldl(fun(FieldName, LastT) ->
    FieldInitNameTs = lists:filter(fun({Name, _}) ->
      Name == FieldName
    end, InitNameTs),

    % TODO: handle error
    1 = length(FieldInitNameTs),
    {_, InitT} = hd(FieldInitNameTs),
    {lam, InitT, LastT}
  end, TV, FieldNamesRev),

  {TV, add_csts({T, FnT}, C2)};

infer({app, Expr, Args}, C) ->
  {ArgTsRev, C1} = lists:foldl(fun(Arg, {Ts, FoldC}) ->
    {T, FoldC1} = infer(Arg, FoldC),
    {[T | Ts], FoldC1}
  end, {[], C}, Args),

  {ExprT, C2} = infer(Expr, C1),
  TV = tv_server:fresh(C2#ctx.pid),
  T = if
    length(ArgTsRev) == 0 -> {lam, none, TV};
    true ->
      lists:foldl(fun(ArgT, LastT) ->
        {lam, ArgT, LastT}
      end, TV, ArgTsRev)
  end,

  {TV, add_csts({T, ExprT}, C2)};

infer({native, {atom, _, Module}, {var, _, Name}, Arity}, C) ->
  % TODO: handle case where this fails
  true = erlang:function_exported(Module, list_to_atom(Name), Arity),
  T = if
    Arity == 0 -> {lam, none, tv_server:fresh(C#ctx.pid)};
    true ->
      lists:foldl(fun(_, LastT) ->
        {lam, tv_server:fresh(C#ctx.pid), LastT}
      end, tv_server:fresh(C#ctx.pid), lists:seq(1, Arity))
  end,

  {T, C};

infer({{'if', _}, Expr, Then, Else}, C) ->
  {ExprT, C1} = infer(Expr, C),
  {ThenT, C2} = infer(Then, C1),

  case Else of
    none -> {none, add_csts([{{con, 'Bool'}, ExprT}], C2)};
    _ ->
      {ElseT, C3} = infer(Else, C2),
      TV = tv_server:fresh(C#ctx.pid),
      {TV, add_csts([{{con, 'Bool'}, ExprT}, {TV, ThenT}, {TV, ElseT}], C3)}
  end;

infer({{'let', _}, Inits, Expr}, C) ->
  C1 = lists:foldl(fun({{var, _, Name}, _}, FoldC) ->
    {TV, ID} = tv_server:fresh_gnr_id(FoldC#ctx.pid),
    % TODO: name conflicts?
    add_env(Name, {add_dep, TV, ID}, FoldC)
  end, C, Inits),

  C2 = lists:foldl(fun({{var, _, Name}, InitExpr}, FoldC) ->
    #{Name := {add_dep, TV, ID}} = FoldC#ctx.env,
    % for generalization, use env that doesn't contain let variables
    {T, FoldC1} = infer(InitExpr, new_gnr(TV, ID, FoldC)),
    FoldC2 = add_csts({TV, T}, FoldC1),
    finish_gnr(FoldC2, FoldC#ctx.gnr)
  end, C1, Inits),

  {T, C3} = infer(Expr, C2),
  {T, C3#ctx{env=C#ctx.env}};

infer({{match, _}, Expr, Cases}, C) ->
  TV = tv_server:fresh(C#ctx.pid),

  C1 = lists:foldl(fun({'case', Pattern, Then}, FoldC) ->
    {ExprT, FoldC1} = infer(Expr, new_gnr(FoldC)),
    {PatternT, FoldC2} = infer(Pattern, start_pattern(FoldC1)),
    FoldC3 = add_csts({ExprT, PatternT}, FoldC2),
    {ThenT, FoldC4} = infer(Then, finish_gnr_pattern(FoldC3, FoldC#ctx.gnr)),

    % revert env to before pattern was parsed
    add_csts([{TV, ThenT}], FoldC4#ctx{env=FoldC#ctx.env})
  end, C, Cases),

  {TV, C1};

infer({block, Exprs}, C) ->
  lists:foldl(fun(Expr, {_, FoldC}) ->
    infer(Expr, FoldC)
  end, {none, C}, Exprs);

infer({{Op, _}, Left, Right}, C) ->
  {LeftT, C1} = infer(Left, C),
  {RightT, C2} = infer(Right, C1),

  TV = tv_server:fresh(C2#ctx.pid),

  Cst = if
    Op == '=='; Op == '!=' ->
      OperandTV = tv_server:fresh(C2#ctx.pid),
      {
        {lam, LeftT, {lam, RightT, TV}},
        {lam, OperandTV, {lam, OperandTV, {con, 'Bool'}}}
      };
    Op == '||'; Op == '&&' -> {
      {lam, LeftT, {lam, RightT, TV}},
      {lam, {con, 'Bool'}, {lam, {con, 'Bool'}, {con, 'Bool'}}}
    };
    Op == '>'; Op == '<'; Op == '>='; Op == '<=' ->
      NumTV = tv_server:fresh('Num', C2#ctx.pid),
      {
        {lam, LeftT, {lam, RightT, TV}},
        {lam, NumTV, {lam, NumTV, {con, 'Bool'}}}
      };
    Op == '+'; Op == '-'; Op == '*'; Op == '/' ->
      NumTV = tv_server:fresh('Num', C2#ctx.pid),
      ReturnT = if Op == '/' -> {con, 'Float'}; true -> NumTV end,
      {
        {lam, LeftT, {lam, RightT, TV}},
        {lam, NumTV, {lam, NumTV, ReturnT}}
      };
    Op == '%' ->
      ReturnTV = tv_server:fresh('Num', C2#ctx.pid),
      {
        {lam, LeftT, {lam, RightT, TV}},
        {lam, {con, 'Int'}, {lam, {con, 'Int'}, ReturnTV}}
      };
    Op == '++' ->
      OperandTV = tv_server:fresh('Concatable', C2#ctx.pid),
      {
        {lam, LeftT, {lam, RightT, TV}},
        {lam, OperandTV, {lam, OperandTV, OperandTV}}
      };
    Op == '--' ->
      OperandTV = tv_server:fresh('Separable', C2#ctx.pid),
      {
        {lam, LeftT, {lam, RightT, TV}},
        {lam, OperandTV, {lam, OperandTV, OperandTV}}
      }
  end,

  {TV, add_csts(Cst, C2)};

infer({{Op, _}, Expr}, C) ->
  {ExprT, C1} = infer(Expr, C),
  TV = tv_server:fresh(C1#ctx.pid),

  Cst = if
    Op == '!' -> {{lam, ExprT, TV}, {lam, {con, 'Bool'}, {con, 'Bool'}}};
    Op == '#' ->
      ElemT = tv_server:fresh(C1#ctx.pid),
      {{lam, ExprT, TV}, {lam, {gen, 'List', ElemT}, {gen, 'Set', ElemT}}};
    Op == '-' ->
      NumT = tv_server:fresh('Num', C1#ctx.pid),
      {{lam, ExprT, TV}, {lam, NumT, NumT}};
    Op == 'discard' -> {TV, none}
  end,

  {TV, add_csts(Cst, C1)}.

add_env(Name, Value, C) ->
  % just a sanity assertion that Value is in the right format
  case Value of
    {add_dep, {tv, _, _, _}, _} -> true;
    {no_dep, {tv, _, _, _}} -> true
  end,
  C#ctx{env=(C#ctx.env)#{Name => Value}}.

new_gnr(C) ->
  ID = tv_server:next_gnr_id(C#ctx.pid),
  G = #gnr{id=ID, env=C#ctx.env, csts=[], deps=[]},
  C#ctx{gnr=G}.

% TODO: just use next_gnr_id in here and get rid of fresh_gnr_id
new_gnr({tv, V, _, _}, ID, C) ->
  G = #gnr{id=ID, vs=[V], env=C#ctx.env, csts=[], deps=[]},
  C#ctx{gnr=G}.

finish_gnr(C, OldG) ->
  C#ctx{gnrs=[C#ctx.gnr | C#ctx.gnrs], gnr=OldG}.

start_pattern(C) ->
  C#ctx{in_pattern=true, pattern_env=#{}}.

finish_gnr_pattern(C, OldG) ->
  G = C#ctx.gnr,
  Vs = maps:fold(fun(_, {tv, V, _, _}, FoldVs) ->
    [V | FoldVs]
  end, [], C#ctx.pattern_env),

  C1 = case length(Vs) of
    % No variables to generalize, so just merge G into OldG.
    0 ->
      OldG1 = OldG#gnr{
        csts=G#gnr.csts ++ OldG#gnr.csts,
        deps=G#gnr.deps ++ OldG#gnr.deps
      },
      C#ctx{gnr=OldG1};

    _ ->
      G1 = G#gnr{vs=Vs},
      PatternEnv = maps:map(fun(_, TV) ->
        {add_dep, TV, G1#gnr.id}
      end, C#ctx.pattern_env),
      NewEnv = maps:merge(C#ctx.env, PatternEnv),
      C#ctx{gnrs=[G1 | C#ctx.gnrs], gnr=OldG, env=NewEnv}
  end,

  C1#ctx{in_pattern=false, pattern_env=undefined}.

add_csts(Csts, C) ->
  G = C#ctx.gnr,
  G1 = case is_list(Csts) of
    true -> G#gnr{csts=Csts ++ G#gnr.csts};
    false -> G#gnr{csts=[Csts | G#gnr.csts]}
  end,

  C#ctx{gnr=G1}.

norm_sig_type(SigT, Pid) ->
  % TODO: is it more intuitive to change each fv to *fv and then replace?
  FVList = gb_sets:to_list(fvs(SigT)),
  NewFVList = lists:map(fun(_) ->
    {all, tv_server:next_name(Pid)}
  end, FVList),
  FVSubs = maps:from_list(lists:zip(FVList, NewFVList)),
  subs(SigT, FVSubs).

lookup(Name, C) ->
  % TODO: handle case where can't find variable
  case maps:find(Name, C#ctx.env) of
    {ok, {add_dep, EnvTV, ID}} ->
      G = C#ctx.gnr,
      G1 = G#gnr{deps=[ID | G#gnr.deps]},

      % We need to defer instantiation until we start solving constraints.
      % Otherwise, we don't know the real types of these variables, and can't
      % instantiate properly.
      {{inst, EnvTV}, C#ctx{gnr=G1}};

    {ok, {_, EnvTV}} -> {EnvTV, C}
  end.

solve(Gs, S) ->
  Map = lists:foldl(fun(G, FoldMap) -> FoldMap#{G#gnr.id => G} end, #{}, Gs),
  ?LOG("Gs", lists:map(fun(G) -> G#gnr{csts=pretty_csts(G#gnr.csts)} end, Gs)),

  T = lists:foldl(fun(#gnr{id=ID}, FoldT) ->
    #{ID := #gnr{index=Index}} = FoldT#tarjan.map,
    if
      Index == undefined -> connect(ID, FoldT#tarjan{stack=[]});
      true -> FoldT
    end
  end, #tarjan{map=Map, next_index=0, solver=S}, Gs),

  case T#tarjan.solver of
    #solver{errs=Errs} when length(Errs) > 0 -> {errors, Errs};
    #solver{subs=Subs} -> {ok, Subs}
  end.

connect(ID, #tarjan{stack=Stack, map=Map, next_index=NextIndex, solver=S}) ->
  #{ID := G} = Map,
  Stack1 = [ID | Stack],
  Map1 = Map#{ID := G#gnr{index=NextIndex, low_link=NextIndex, on_stack=true}},

  T1 = #tarjan{stack=Stack1, map=Map1, next_index=NextIndex + 1, solver=S},
  T2 = lists:foldl(fun(AdjID, FoldT) ->
    #{AdjID := #gnr{index=AdjIndex, on_stack=AdjOnStack}} = FoldT#tarjan.map,

    if
      AdjIndex == undefined ->
        FoldT1 = connect(AdjID, FoldT),
        FoldMap1 = FoldT1#tarjan.map,
        #{ID := FoldG1, AdjID := AdjG1} = FoldMap1,
        FoldG2 = FoldG1#gnr{
          low_link=min(FoldG1#gnr.low_link, AdjG1#gnr.low_link)
        },
        FoldT1#tarjan{map=FoldMap1#{ID := FoldG2}};

      AdjOnStack ->
        FoldMap = FoldT#tarjan.map,
        #{ID := FoldG} = FoldMap,
        FoldG1 = FoldG#gnr{
          low_link=min(FoldG#gnr.low_link, AdjIndex)
        },
        FoldT#tarjan{map=FoldMap#{ID := FoldG1}};

      true -> FoldT
    end
  end, T1, G#gnr.deps),

  #tarjan{stack=Stack2, map=Map2, solver=S2} = T2,
  #{ID := G2} = Map2,
  if
    G2#gnr.low_link == G2#gnr.index ->
      {Popped, Left} = lists:splitwith(fun(StackID) ->
        StackID /= ID
      end, Stack2),
      SolvableIDs = [ID | Popped],

      Map3 = lists:foldl(fun(SolID, FoldMap) ->
        #{SolID := SolG} = FoldMap,
        FoldMap#{SolID := SolG#gnr{on_stack=false}}
      end, Map2, SolvableIDs),

      ?LOG("Solvable IDs", SolvableIDs),

      S3 = lists:foldl(fun(SolID, FoldS) ->
        #{SolID := SolG} = Map3,
        unify_csts(SolG, FoldS)
      end, S2, SolvableIDs),

      ?LOG("Subs", S3#solver.subs),

      S4 = lists:foldl(fun(SolID, FoldS) ->
        #{SolID := SolG} = Map3,

        lists:foldl(fun(SolV, NestedS) ->
          #solver{subs=Subs, schemes=Schemes} = NestedS,
          SolTV = {tv, SolV, none, any},
          T = subs(SolTV, Subs),
          {GVs, GT} = generalize(T, SolG#gnr.env),
          Schemes1 = Schemes#{SolV => {GVs, GT}},

          % don't want to sub SolTV for itself and create an infinite loop
          Subs1 = if SolTV == T -> Subs; true -> Subs#{SolV => GT} end,
          NestedS#solver{subs=Subs1, schemes=Schemes1}
        end, FoldS, SolG#gnr.vs)
      end, S3, SolvableIDs),

      T2#tarjan{stack=tl(Left), map=Map3, solver=S4};

    true -> T2
  end.

unify_csts(#gnr{csts=Csts, env=Env}, S) ->
  RigidVs = maps:fold(fun(_, Value, FoldVs) ->
    case Value of
      {no_dep, T} -> gb_sets:union(FoldVs, fvs(T));
      {add_dep, _, _} -> FoldVs
    end
  end, gb_sets:new(), Env),

  % Constraints are always prepended to the list in a depth-first manner. Hence,
  % the shallowest expression's constraints come first. We'd like to solve the
  % deepest expression's constraints first to have better error messages (e.g.
  % rather than can't unify [A] with B, can't unify [Float] with Bool), so we
  % reverse the order here.
  OrderedCsts = lists:reverse(Csts),

  lists:foldl(fun({L, R}, FoldS) ->
    Subs = FoldS#solver.subs,
    L1 = subs(resolve(L, FoldS), Subs),
    R1 = subs(resolve(R, FoldS), Subs),
    unify({L1, R1}, FoldS)
  end, S#solver{rigid_vs=RigidVs}, OrderedCsts).

resolve({lam, ArgT, ReturnT}, S) ->
  {lam, resolve(ArgT, S), resolve(ReturnT, S)};
resolve({tuple, LeftT, RightT}, S) ->
  {tuple, resolve(LeftT, S), resolve(RightT, S)};
resolve({tv, V, I, Cat}, _) -> {tv, V, I, Cat};
resolve({con, Con}, _) -> {con, Con};
resolve({gen, Con, ParamT}, S) -> {gen, Con, resolve(ParamT, S)};
resolve({inst, TV}, S) ->
  {tv, V, _, _} = TV,
  ResolvedT = case maps:find(V, S#solver.schemes) of
    {ok, Scheme} -> inst(Scheme, S);
    % Not sure if we should resolve() or not here to make inst vars rigid.
    error -> TV
  end,
  resolve(ResolvedT, S);
resolve(none, _) -> none.

inst({GVs, T}, S) ->
  Subs = gb_sets:fold(fun(V, FoldSubs) ->
    FoldSubs#{V => tv_server:next_name(S#solver.pid)}
  end, #{}, GVs),
  subs(T, Subs).

generalize(T, Env) ->
  EnvFVs = maps:fold(fun(_, Value, S) ->
    EnvTV = case Value of
      {no_dep, TV} -> TV;
      {add_dep, TV, _} -> TV
    end,
    gb_sets:union(fvs(EnvTV), S)
  end, gb_sets:new(), Env),
  GVs = gb_sets:subtract(fvs(T), EnvFVs),

  % for normalization, change all all(TV) to TV
  Subs = gb_sets:fold(fun(FoldV, FoldSubs) ->
    FoldSubs#{FoldV => any}
  end, #{}, GVs),
  {GVs, subs(T, Subs)}.

unify({T1, T2}, S) when T1 == T2 -> S;

unify({{lam, ArgT1, ReturnT1}, {lam, ArgT2, ReturnT2}}, S) ->
  S1 = unify({ArgT1, ArgT2}, S),
  ToUnify = {subs(ReturnT1, S1#solver.subs), subs(ReturnT2, S1#solver.subs)},
  unify(ToUnify, S1);
unify({{tuple, LeftT1, RightT1}, {tuple, LeftT2, RightT2}}, S) ->
  S1 = unify({LeftT1, LeftT2}, S),
  ToUnify = {subs(RightT1, S1#solver.subs), subs(RightT2, S1#solver.subs)},
  unify(ToUnify, S1);

unify({{tv, V, I1, Cat1}, {tv, V, I2, Cat2}}, _) ->
  error({badarg, V, I1, Cat1, I2, Cat2});
unify({{tv, V1, I1, Cat1}, {tv, V2, I2, Cat2}}, S) ->
  TV1 = {tv, V1, I1, Cat1},
  TV2 = {tv, V2, I2, Cat2},

  Ilk1 = ilk(TV1, S),
  Ilk2 = ilk(TV2, S),
  Occurs = occurs(V1, TV2),

  if
    Occurs -> add_err({TV1, TV2}, S);

    % any(X: I1) ~ rigid(Y: I2) or any(X: I1) ~ all(Y: I2) or
    % rigid(X: I1) ~ rigid(Y: I2) if I1 <= I2.
    (Ilk1 == any) or ((Ilk1 == rigid) and (Ilk2 == rigid)),
    (I1 == none) or (I1 == I2) ->
      add_sub(V1, TV2, S);

    % rigid(X: I1) ~ any(Y: I2) or all(X: I1) ~ any(Y: I2) or
    % rigid(X: I1) ~ rigid(Y: I2) if I1 >= I2.
    (Ilk2 == any) or ((Ilk1 == rigid) and (Ilk2 == rigid)),
    (I2 == none) or (I1 == I2) ->
      add_sub(V2, TV1, S);

    % any(X: I) ~ rigid(Y) so long as we convert both to rigid(Y: I).
    % Note we must keep the same rigid type variable name Y.
    Ilk1 == any, Ilk2 == rigid, I2 == none ->
      add_sub(V2, {set_iface, I1}, add_sub(V1, TV2, S));

    % rigid(X) ~ any(Y: I) so long as we convert both to rigid(X: I).
    % Note we must keep the same rigid type variable name X.
    Ilk2 == any, Ilk1 == rigid, I1 == none ->
      add_sub(V1, {set_iface, I2}, add_sub(V2, TV1, S));

    true -> add_err({{tv, V1, I1, Ilk1}, {tv, V2, I2, Ilk2}}, S)
  end;
unify({{tv, V, I, Cat}, T}, S) ->
  TV = {tv, V, I, Cat},
  Ilk = ilk(TV, S),

  Err = {TV, T},
  Occurs = occurs(V, T),
  Instance = (I == none) or instance(T, I),
  HasTV = occurs(any, T),

  if
    Occurs -> add_err(Err, S);
    (Ilk == all) or ((Ilk == rigid) and HasTV) ->
      add_err({{tv, V, I, Ilk}, T}, S);
    Instance -> add_sub(V, T, S);
    true -> add_err(Err, S)
  end;
unify({T, {tv, V, I, Cat}}, S) -> unify({{tv, V, I, Cat}, T}, S);

unify({{gen, C, ParamT1}, {gen, C, ParamT2}}, S) ->
  unify({ParamT1, ParamT2}, S);

unify({T1, T2}, S) -> S#solver{errs=[{T1, T2} | S#solver.errs]}.

add_sub(Key, Value, S) ->
  case maps:find(Key, S#solver.subs) of
    {ok, Existing} -> error({badarg, Key, Existing, Value});
    error -> S#solver{subs=(S#solver.subs)#{Key => Value}}
  end.

add_err(Err, S) ->
  S#solver{errs=[Err | S#solver.errs]}.

ilk({tv, V, _, Cat}, S) ->
  case gb_sets:is_member(V, S#solver.rigid_vs) of
    true ->
      any = Cat,
      rigid;
    false -> Cat
  end.

instance({con, 'Int'}, 'Num') -> true;
instance({con, 'Float'}, 'Num') -> true;
instance({con, 'String'}, 'Concatable') -> true;
instance({gen, 'List', _}, 'Concatable') -> true;
instance({gen, 'Map', _}, 'Concatable') -> true;
instance({gen, 'Set', _}, 'Concatable') -> true;
instance({gen, 'List', _}, 'Separable') -> true;
instance({gen, 'Set', _}, 'Separable') -> true;
instance(_, _) -> false.

subs({lam, ArgT, ReturnT}, Subs) ->
  {lam, subs(ArgT, Subs), subs(ReturnT, Subs)};
subs({tuple, LeftT, RightT}, Subs) ->
  {tuple, subs(LeftT, Subs), subs(RightT, Subs)};
subs({tv, V, I, Cat}, Subs) ->
  case maps:find(V, Subs) of
    error -> {tv, V, I, Cat};
    {ok, any} -> {tv, V, I, any};
    {ok, {all, V1}} -> {tv, V1, I, all};

    {ok, {set_iface, I1}} ->
      any = Cat,
      {tv, V, I1, Cat};

    {ok, Value} ->
      Sub = if
        % Replacing with a new type entirely
        is_tuple(Value) or (Value == none) -> Value;
        % Instantiation, so category resets to any
        true -> {tv, Value, I, any}
      end,
      subs(Sub, Subs)
  end;
subs({con, Con}, _) -> {con, Con};
subs({gen, Con, ParamT}, Subs) -> {gen, Con, subs(ParamT, Subs)};
subs({inst, TV}, Subs) -> {inst, subs(TV, Subs)};
subs(none, _) -> none.

fvs({lam, ArgT, ReturnT}) -> gb_sets:union(fvs(ArgT), fvs(ReturnT));
fvs({tuple, LeftT, RightT}) -> gb_sets:union(fvs(LeftT), fvs(RightT));
fvs({tv, V, _, _}) -> gb_sets:from_list([V]);
fvs({con, _}) -> gb_sets:new();
fvs({gen, _, ParamT}) -> fvs(ParamT);
% fvs({inst, ...}) ommitted; they should be resolved
fvs(none) -> gb_sets:new().

occurs(V, {lam, ArgT, ReturnT}) ->
  occurs(V, ArgT) or occurs(V, ReturnT);
occurs(V, {tuple, LeftT, RightT}) ->
  occurs(V, LeftT) or occurs(V, RightT);
occurs(V, {tv, V1, _, _}) -> (V == any) or (V == V1);
occurs(_, {con, _}) -> false;
occurs(V, {gen, _, ParamT}) -> occurs(V, ParamT);
% occurs({inst, ...}) ommitted; they should be resolved
occurs(_, none) -> false.

pretty_csts([]) -> [];
pretty_csts([{L, R} | Rest]) ->
  [{pretty(L), pretty(R)} | pretty_csts(Rest)].

pretty({lam, ArgT, ReturnT}) ->
  Format = case ArgT of
    {lam, _, _} -> "(~s) -> ~s";
    _ -> "~s -> ~s"
  end,
  format_str(Format, [pretty(ArgT), pretty(ReturnT)]);
pretty({tuple, LeftT, RightT}) ->
  format_str("(~s, ~s)", [pretty(LeftT), pretty_strip_parens(RightT)]);
pretty({tv, V, I, Ilk}) ->
  Str = if
    I == none -> tl(V);
    true -> format_str("~s: ~s", [tl(V), atom_to_list(I)])
  end,

  case Ilk of
    any -> Str;
    rigid -> format_str("rigid(~s)", [Str]);
    all -> format_str("all(~s)", [Str])
  end;
pretty({con, Con}) -> atom_to_list(Con);
pretty({gen, 'List', ParamT}) ->
  format_str("[~s]", [pretty_strip_parens(ParamT)]);
pretty({gen, T, ParamT}) ->
  format_str("~s<~s>", [atom_to_list(T), pretty_strip_parens(ParamT)]);
pretty({inst, TV}) ->
  format_str("inst(~s)", [pretty(TV)]);
pretty(none) -> "()".

pretty_strip_parens({tuple, LeftT, RightT}) ->
  format_str("~s, ~s", [pretty(LeftT), pretty_strip_parens(RightT)]);
pretty_strip_parens(T) -> pretty(T).

format_str(Str, Args) ->
  lists:flatten(io_lib:format(Str, Args)).
