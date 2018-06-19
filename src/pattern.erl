-module(pattern).
-export([names/1, vars/1, check_exhaustive/3]).
-include("common.hrl").

names(Pattern) -> [Name || {var, _, Name} <- vars(Pattern)].

vars(T) -> vars(T, []).

vars({N, _, _}, L) when N == int; N == float; N == bool; N == char;
  N == str; N == atom -> L;
vars({var, _, _}=Var, L) -> [Var | L];
vars({N, _}, L) when N == unit; N == '_' -> L;
% {field, ...} is unnecessary because it's only ever contained within variant,
% and we don't recurse on it below.
vars({variant, _, _, Args}, L) ->
  lists:foldr(fun vars/2, L, Args);
vars({list, _, Elems}, L) ->
  lists:foldr(fun vars/2, L, Elems);
vars({cons, _, Elems, Tail}, L) ->
  lists:foldr(fun vars/2, vars(Tail, L), Elems);
vars({tuple, _, Elems}, L) ->
  lists:foldr(fun vars/2, L, Elems).

check_exhaustive(Patterns, T, S) ->
  V = tv_server:next_name(S#solver.pid),
  Ts = #{V => T},
  check_cases([{pv, V}], Patterns, Ts, S).

check_cases([], _, _, S) -> S;
check_cases([Case | Cases], Patterns, Ts, S) ->
  case check(Case, Patterns) of
    true -> check_cases(Cases, Patterns, Ts, S);
    false -> add_case_err(Case, S);
    {expand, Vs} ->
      case find_expansions(Vs, Ts, S) of
        none -> add_case_err(Case, S);
        {V, Expansions, NewTs} ->
          MoreCases = [replace(Case, V, Expan) || Expan <- Expansions],
          check_cases(MoreCases ++ Cases, Patterns, NewTs, S)
      end
  end.

check(_, []) -> false;
check(Case, [Pattern | Patterns]) ->
  case matches(Case, Pattern) of
    true -> true;
    false -> check(Case, Patterns);
    {expand, Vs}=Expand ->
      case check(Case, Patterns) of
        true -> true;
        false -> Expand;
        {expand, MoreVs} -> {expand, ordsets:union(Vs, MoreVs)}
      end
  end.

matches(_, {var, _, _}) -> true;
matches(_, {'_', _}) -> true;
matches({}, {unit, _}) -> true;
matches(true, {bool, _, true}) -> true;
matches(false, {bool, _, false}) -> true;
matches([], {list, _, []}) -> true;
matches({cons, Elem1, Tail1}, {list, Loc, [Elem2 | Tail2]}) ->
  matches([{Elem1, Elem2}, {Tail1, {list, Loc, Tail2}}]);
matches({cons, Elem1, Tail1}, {cons, Loc, [Elem2 | Rest], Tail2}) ->
  case Rest of
    [] -> matches([{Elem1, Elem2}, {Tail1, Tail2}]);
    _ -> matches([{Elem1, Elem2}, {Tail1, {cons, Loc, Rest, Tail2}}])
  end;
matches({tuple, Elems1}, {tuple, _, Elems2}) ->
  matches(lists:zip(Elems1, Elems2));
matches({variant, Con, Args1}, {variant, _, Expr, Args2}) ->
  ConMatches = case Expr of
    % Don't need to check Module here; this has already passed typechecking.
    {field, _, _, {con_token, _, Con}} -> true;
    {con_token, _, Con} -> true;
    _ -> false
  end,

  case ConMatches of
    true -> matches(lists:zip(Args1, Args2));
    false -> false
  end;
matches({pv, V}, _) -> {expand, ordsets:from_list([V])};
matches(_, _) -> false.

matches([]) -> true;
matches([{Case, Pattern} | CasePatterns]) ->
  case matches(Case, Pattern) of
    true -> matches(CasePatterns);
    false -> false;
    {expand, Vs}=Expand ->
      case matches(CasePatterns) of
        true -> Expand;
        false -> false;
        {expand, MoreVs} -> {expand, ordsets:union(Vs, MoreVs)}
      end
  end.

find_expansions([], _, _) -> none;
find_expansions([V | Vs], Ts, S) ->
  case maps:find(V, Ts) of
    error -> find_expansions(Vs, Ts, S);
    {ok, T} ->
      case expansions(T, Ts, S) of
        none -> find_expansions(Vs, Ts, S);
        {Expansions, NewTs} -> {V, Expansions, NewTs}
      end
  end.

expansions({con, "()"}, Ts, _) -> {[{}], Ts};
expansions({con, "Bool"}, Ts, _) -> {[true, false], Ts};
expansions({gen, {con, "List"}, [ParamT]}=ListT, Ts, #solver{pid=Pid}) ->
  ParamV = tv_server:next_name(Pid),
  ListV = tv_server:next_name(Pid),
  NewTs = Ts#{ParamV => ParamT, ListV => ListT},
  {[[], {cons, {pv, ParamV}, {pv, ListV}}], NewTs};
expansions({tuple, ElemTs}, Ts, #solver{pid=Pid}) ->
  {ElemPVs, NewTs} = lists:mapfoldl(fun(ElemT, FoldTs) ->
    ElemV = tv_server:next_name(Pid),
    {{pv, ElemV}, FoldTs#{ElemV => ElemT}}
  end, Ts, ElemTs),
  {[{tuple, ElemPVs}], NewTs};
expansions({con, Con}, Ts, S) -> expansions({gen, {con, Con}, []}, Ts, S);
expansions({gen, {con, Con}, ParamTs}, Ts, S) ->
  #solver{aliases=Aliases, enums=Enums} = S,
  case maps:find(Con, Enums) of
    error -> none;
    {ok, {Variants, Vs}} ->
      Subs = maps:from_list(lists:zip(Vs, ParamTs)),

      lists:mapfoldl(fun(Variant, FoldTs) ->
        #variant{
          con=VariantCon,
          effective_t=EffectiveT,
          has_tvs=HasTVs
        } = Variant,

        SubbedT = case HasTVs of
          true -> utils:subs(EffectiveT, #sub_opts{subs=Subs, aliases=Aliases});
          false -> EffectiveT
        end,
        case SubbedT of
          {con, "Atom"} -> {{variant, VariantCon, []}, FoldTs};
          {tuple, [{con, "Atom"} | ElemTs]} ->
            {[{tuple, ElemPVs}], NewTs} = expansions({tuple, ElemTs}, Ts, S),
            {{variant, VariantCon, ElemPVs}, NewTs}
        end
      end, Ts, Variants)
  end;
expansions(_, _, _) -> none.

replace({cons, Elem, Tail}, V, Expan) ->
  {cons, replace(Elem, V, Expan), replace(Tail, V, Expan)};
replace({tuple, Elems}, V, Expan) ->
  {tuple, [replace(E, V, Expan) || E <- Elems]};
replace({variant, Con, Args}, V, Expan) ->
  {variant, Con, [replace(Arg, V, Expan) || Arg <- Args]};
replace({pv, V}, V, Expan) -> Expan;
replace(Case, _, _) -> Case.

add_case_err(Case, S) ->
  Err = ?ERR_MISSING_CASE(case_str(Case)),
  {false, S1} = type_system:add_err(Err, S),
  S1.

case_str({}) -> "()";
case_str(true) -> "true";
case_str(false) -> "false";
case_str([]) -> "[]";
case_str({cons, _, _}=Cons) ->
  {Elems, Tail} = collect_elems(Cons),
  ElemsStr = lists:join(", ", [case_str(E) || E <- Elems]),

  case Tail of
    [] -> [$[, ElemsStr, $]];
    _ -> [$[, ElemsStr, " | ", case_str(Tail), $]]
  end;
case_str({tuple, Elems}) ->
  [$(, lists:join(", ", [case_str(E) || E <- Elems]), $)];
case_str({variant, Con, Args}) ->
  if
    Args == [] -> Con;
    true -> [Con, $(, lists:join(", ", [case_str(Arg) || Arg <- Args]), $)]
  end;
case_str({pv, _}) -> "_".

collect_elems({cons, Elem, Tail}) ->
  {Elems, FinalTail} = collect_elems(Tail),
  {[Elem | Elems], FinalTail};
collect_elems(Tail) -> {[], Tail}.
