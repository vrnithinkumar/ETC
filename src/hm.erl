-module(hm).
-export([solve/1,solvePreds/2]).
-export([unify/2]).
-export([emptySub/0,comp/2,subE/2
    ,subT/2,subP/2
    ,subPs/2,free/1
    ,isTVar/1]).
-export([bt/2,funt/3,tvar/2,tcon/3,forall/4, tMeta/4, tSkol/2]).
-export([freshTMeta/3, freshTMeta/4, freshTSkol/1, replaceFreshTMeta/2, generalizeType/1]).
-export([freshen/1,generalize/3,eqType/2,fresh/1, specialize/2]).
-export([getLn/1,pretty/1,prettyCs/2,prettify/2,replaceLn/2, replaceLn/3]).
-export([is_same/2, isSubType/2, get_all_class_types/1]).
-export([has_type_var/1, is_type_var/1, type_without_bound/1]).
-export([get_fn_args/1, get_fn_rt/1, generalizeSpecT/2]).
-export([getListType/2, getTupleType/2, metaTupleTypeOfN/3]).
-export_type([constraint/0,type/0]).

-type tvar() :: any().
-type sub() :: maps:map(). % Map <tvar(),type()>

-type constraint() :: {type(), type()}.

-type class() :: string().
-type predicate() :: {class, class(), type()} | {oc, type(),[type()]}.

%% PRINT Debugging macro%%
-ifndef(PRINT).
-define(PRINT(Var), io:format("DEBUG: ~p:~p - ~p~n~n ~p~n~n", [?MODULE, ?LINE, ??Var, Var])).
-endif.

%%%%%%%%%%%%% Type variable constructors

-type type() :: 
    {bt, integer(), type()}
    | {funt, integer(), [type()], type()}
    | {tvar, integer(), type()}
    | {tcon, integer(), string(),[type()]}
    | {forall, type(), [predicate()], type()}
    | {whilst, [predicate()], type()}
    | {tMeta, integer(), type(), [type()], type(), boolean()}
    | {tSkol, type()}.

% L is line/length
bt(A,L)                 -> {bt, L, A}. % A arguments , B is return type
funt(As,B,L)            -> {funt, L, As, B}. % A arguments list , B is return type
tvar(A,L)               -> {tvar, L, A}. % L = Line, A : Name of the variable
tcon(N,As,L)            -> {tcon, L, N, As}. % N:Name of the constructor A: args
forall(X,Ps,A,L)        -> {forall, tvar(X,L), Ps, A}. %P for predicates
tMeta(Id, Tvs, Mono, L) -> {tMeta, L, Id, Tvs, null, Mono}.
tSkol(Id, L)            -> {tSkol, L, Id}.
%%%%%%%%%%%% Constraint solver

-spec solve([constraint()]) -> sub().
solve(Cs) -> solve(Cs, emptySub()).

-spec solve([constraint()], sub()) -> sub().
solve ([],Sub) -> Sub;
solve ([{T1,T2}|Cs],Sub) ->
    Sub_ = unify(T1,T2),
    solve(
        % apply new substitution to remaining constraints
        lists:map(fun(Cx) -> subC(Cx, Sub_) end, Cs), 
        % compose substitutions
        comp(Sub_,Sub)).

%%%%%%%%%%%% Unification algorithm

-spec unifyMany([type()],[type()]) -> sub().
unifyMany([],[])            -> emptySub();
unifyMany([],_)             -> erlang:error({type_error, "arg_mismatch"});
unifyMany(_,[])             -> erlang:error({type_error, "arg_mismatch"});
unifyMany ([A|As],[B|Bs])   ->
    Sub = unify(A,B),
    As_ = lists:map(fun(T) -> subT(T,Sub) end, As),
    Bs_ = lists:map(fun(T) -> subT(T,Sub) end, Bs),
    comp(unifyMany(As_,Bs_),Sub).

% unify is left biased (this is a crucial property relied upon!)
% i.e., unify(T1,T2) returns substitution for T1 in terms of T2
-spec unify(type(), type()) -> sub().
unify ({funt,L1,As1, B1}, {funt,L2,As2, B2}) ->
    try
        unifyMany (As1, As2)
    of
        X -> 
            Y = unify (subT(B1, X),subT(B2, X)),
            comp(Y,X)
    catch
        error:{type_error,"arg_mismatch"} -> erlang:error({type_error, 
                                    "Number of arguments to function on line " ++ util:to_string(L1) ++ " do not match"
                                    ++ " arguments on line " ++ util:to_string(L2)})
    end;
unify ({tvar,L,V},T) ->
    Eq  = eqType({tvar, L,V}, T),
    Occ = occurs(V,T),
    if
        Eq              -> emptySub();
        Occ             -> 
            erlang:error({type_error,
                                "Failed occurs check on line " ++ util:to_string(L)});
        true            -> maps:put(V,T,emptySub())
    end;
unify (T,{tvar,L,V}) ->
    unify ({tvar,L,V},T);
unify({tcon,L1,N1,As1},{tcon,L2,N2,As2}) ->
    case N1 == N2 of
        true        -> 
            try
                unifyMany(As1,As2)
            catch   
                error:{type_error,"arg_mismatch"} -> erlang:error({type_error, 
                                    "Number of arguments to type constructor on line " ++ util:to_string(L1) ++ " do not match"
                                    ++ " arguments on line " ++ util:to_string(L2)})
            end;
        false       -> erlang:error({type_error,
                        "Cannot unify "++ util:to_string(N1) 
                        ++ " (on line "++ util:to_string(L1) ++")"
                        ++" with " ++ util:to_string(N2) 
                        ++ " (on line "++ util:to_string(L2) ++")"})
    end;
unify (T,U) ->
    Eq = eqType(T,U),
    if
        Eq          -> emptySub();
        true        -> erlang:error({type_error, 
                            "Cannot unify " ++ util:to_string(T) ++ 
                            " with " ++ util:to_string(U)})
    end.

-spec eqType(type(),type()) -> boolean().
eqType({bt,_,A}, {bt,_,B}) -> A == B;
% hack for string to char[] check
eqType({bt,_,string}, {tcon,_, "List", [{bt, _, char}]}) -> true;
eqType({tcon,_, "List", [{bt, _, char}]}, {bt,_,string}) -> true;
eqType({tvar,_,X}, {tvar,_,Y}) -> X == Y;
eqType({funt,_,As1, B1}, {funt,_,As2, B2}) ->
    eqType(B1,B2) andalso util:eqLists(fun eqType/2,As1,As2);
eqType({tcon,_,N1,As1},{tcon,_,N2,As2}) ->
    (N1 == N2) andalso util:eqLists(fun eqType/2,As1,As2);
eqType(_,_) -> false.

%%%%%%%%%%%% Utilities

-spec isTVar(type()) -> boolean().
isTVar({tvar, _L, _}) -> true;
isTVar(_)             -> false.

-spec getLn(type()) -> integer().
getLn ({bt, L, _})                   -> L;
getLn ({funt, L, _, _})              -> L;
getLn ({tvar, L, _})                 -> L;
getLn ({tcon, L, _, _})              -> L;
getLn ({forall, {tvar, L, _}, _, _}) -> L;
getLn ({whilst, _, T})               -> getLn(T);
getLn ({tMeta, L, _, _, _, _})       -> L;
getLn ({tSkol, L, _})                -> L.

-spec replaceLn(type(),integer(),integer()) -> type().
replaceLn ({bt, L0, X},L0,L1)         -> {bt, L1, X};
replaceLn ({funt, L0, As, B},L0,L1)   -> 
    {funt, L1, lists:map(fun(A) -> replaceLn(A,L0,L1) end, As), replaceLn(B,L0,L1)};
replaceLn ({tvar, L0, X},L0,L1)       -> {tvar, L1, X};
replaceLn ({tcon, L0, N, Args},L0,L1)    -> 
    {tcon, L1, N, lists:map(fun(A) -> replaceLn(A,L0,L1) end, Args)};
replaceLn (T,_,_)                    -> T.

-spec replaceLn(type(),integer()) -> type().
replaceLn(Type, NewLn) ->
    OldLn = getLn(Type),
    replaceLn(Type, OldLn, NewLn).

-spec fresh(integer()) -> type().
fresh(L) -> tvar(make_ref(), L).

-spec emptySub() -> sub().
emptySub () -> maps:new().

% Compose two substitutions
-spec comp(sub(), sub()) -> sub().
comp (X,Y) ->
    Y_ = maps:map( % apply substitution X on every entry in Y
            fun(_,Type) -> subT(Type,X) end, Y),
    maps:merge(X,Y_).   % union (Y_, entries in X whose keys are not in Y)

% Apply a substitution to a type
-spec subT(type(), sub()) -> type().
subT ({tvar, L, X}, Sub)  ->
    case maps:is_key(X,Sub) of
        true    ->  maps:get(X,Sub);
        false   ->  {tvar, L, X}
    end;
subT ({bt, L, T}, _)  ->
    {bt, L, T};
subT ({funt, L, As, B}, Sub)   ->
    {funt, L, lists:map(fun(A) -> subT (A,Sub) end, As), subT(B,Sub)};
subT ({tcon, L, N, As}, Sub)   ->
    {tcon, L, N, lists:map(fun(A) -> subT (A,Sub) end, As)};
subT ({forall, {tvar, L, X}, Ps, A}, Sub)   ->
    case maps:is_key(X,Sub) of
        true    ->  {forall, {tvar, L, X}, subPs(Ps,Sub) ,subT(A,maps:remove(X,Sub))};  % avoids name capture!
        false   ->  {forall, {tvar, L, X}, subPs(Ps,Sub) ,subT(A,Sub)}
    end;
subT ({whilst,Ps,T},Sub) -> {whilst,subPs(Ps,Sub),subT(T,Sub)};
%% VR todo added
subT ({tMeta, L, Id, Tvs, T, Mono},Sub) ->
    case T of
        null -> {tMeta, L, Id, Tvs, T, Mono};
        _    -> {tMeta, L, Id, Tvs, subT(T,Sub), Mono}
    end;
subT ({tSkol, L, Id}, _) ->
    {tSkol, L, Id};
%% TODO VR : Fix how to support multiple definitions%%
subT ([Type|_Rest], Sub) -> subT(Type, Sub).


% Repetitive substution on a constraint
-spec subC(constraint(), sub()) -> constraint().
subC ({T1,T2},S) -> {subT(T1,S),subT(T2,S)}.

% Repetitive substution on a predicate
-spec subP(predicate(), sub()) -> predicate().
subP ({class,C,T},S) -> {class,C,subT(T,S)};
subP ({oc,T,MatcingTypes},S) -> 
    {oc, subT(T,S), lists:map(fun(MT)-> subT(MT,S) end, MatcingTypes)}.

% Repetitive substution on a predicate
-spec subPs([predicate()], sub()) -> predicate().
subPs (Ps,S) -> lists:map(fun(P) -> subP(P,S) end, Ps).

% Repetitive substution on an environment
-spec subE(env:env(), sub()) -> env:env().
subE (Env,S) -> env:fmapV(fun(T) -> subT(T,S) end, Env).

-spec occurs(tvar(), type()) -> boolean().
occurs (V,{funt, _, As, B}) ->
    lists:any(fun(A) -> occurs(V,A) end, As) or occurs(V,B);
occurs (_,{bt,_,_}) ->
    false;
occurs (V,{tvar,_, X}) ->
    V == X;
occurs (V,{tcon,_,_,As}) ->
    lists:any(fun(A) -> occurs(V,A) end, As).

% All free type variables in the given type
-spec free(type()) -> set:set(tvar()).
free ({bt, _, _})          -> sets:new();
free ({funt, _, As, B})     -> 
    sets:union(
        lists:foldr(
            fun(A, AccSet) -> sets:union(free(A),AccSet) end
            , sets:new(), As)
        , free (B));
free ({tvar, _, A})        -> sets:add_element(A,sets:new());
free ({tcon, _, _, As})    -> 
    lists:foldr(
        fun(A, AccSet) -> sets:union(free(A),AccSet) end
    , sets:new(), As);
free ({forall, {tvar, _, X}, _, A}) 
                        -> sets:del_element(X, free(A));
free ({whilst,_,T})         -> free(T).


-spec freeInPs([predicate()]) -> set:set(tvar()).
freeInPs(Ps) ->
    lists:foldl(fun(P,AccFree)-> 
            case P of 
                {oc,CT,MTs}   -> 
                    Free = lists:foldl(fun(MT,AccFree_) -> 
                        sets:union(AccFree_,free(MT))
                    end, free(CT), MTs),
                    sets:union(AccFree,Free);
                {class,_,T}   -> sets:union(AccFree,free(T))
            end
        end, sets:new(), Ps).

% converts a mono type to a poly type
-spec generalize(type(),env:env(),[predicate()]) -> type().
generalize (Type,Env,Ps) ->
    MonoVars = sets:union(free(Type),freeInPs(Ps)),
    BoundInEnv = env:freeInEnv(Env),
    % Generalizable variables of a type are
    % monotype variables that are not bound in environment
    Generalizable = sets:subtract(MonoVars, BoundInEnv),
    bindGVs(sets:to_list(Generalizable),Type,Ps).

% bind generalized variables
-spec bindGVs([tvar()],type(),[predicate()]) -> type().
bindGVs ([],T,Ps)      -> {whilst, getUniPreds(Ps),T};
bindGVs ([X|Xs],T,Ps)  -> {forall, {tvar,getLn(T), X}, getClassPredsOn(Ps,{tvar,getLn(T),X}), bindGVs(Xs,T,Ps)}.

-spec bound(type()) -> [{tvar(),integer()}].
bound ({forall, {tvar,L,X},_, A}) -> [{X,L} | bound(A)];
bound (_) -> [].

-spec stripbound(type()) -> {type(),[predicate()]}.
stripbound ({forall, {tvar, _,_}, Ps, A}) -> 
    {T,Ps_} = stripbound(A),
    {T,Ps ++ Ps_};
stripbound ({whilst,UPs,T}) -> {T,UPs};
stripbound (T) -> {T,[]}.

% replace all bound variables with fresh variables
-spec freshen (type()) -> {type(), [predicate()]}.
freshen (T) ->
    BoundVars = bound(T),
    % substitution with a fresh variable for every bound variable
    Sub = lists:foldr(
        fun({V,L}, SAcc)->
            comp(SAcc, maps:put(V,hm:fresh(L),emptySub()))
        end, emptySub(), BoundVars),
    {StrippedT, Ps} = stripbound(T),
    { subT(StrippedT, Sub)
    , subPs(Ps,Sub)}.

% get predicates on a certain type
-spec getClassPredsOn([predicate()],type()) -> [predicate()].
getClassPredsOn(Ps,T) -> 
    lists:filter(fun(P) ->
        case P of
            {class,_,X} -> eqType(T,X);
            _           -> false
        end
    end,Ps).

% get all unification predicates
-spec getUniPreds([predicate()]) -> [predicate()].
getUniPreds(Ps) -> 
    lists:filter(fun(P) ->
        case P of
            {oc,_,_} -> true;
            _           -> false
        end
    end,Ps).

% Predicate solver (proxy)
-spec solvePreds([predicate()],[predicate()]) -> {sub(),[predicate()]}.
solvePreds(Premise,Ps) -> ps:psMain(Premise,Ps).

-spec bound_constraints(type()) -> [{tvar(), [predicate()]}].
bound_constraints({forall, {tvar,_, X}, C, A}) ->
    [{X, C} | bound_constraints(A)];
bound_constraints(_) -> [].

-spec specialize(type(), [hm:type()]) -> {hm:type()}.
specialize(T, STs) ->
    BoundVars = bound_constraints(T),
    CanSpec = can_specialize(BoundVars, STs),
    {StrippedT, Ps} = stripbound(T),
    case CanSpec of
        true -> 
            RT = replace_with_type(T, STs),
            ?PRINT(RT),
            RT;
        false -> erlang:error({type_error,
        "Cannot specialize "++ pretty(T)})
    end.

replace_with_type(T, Ts) ->
    BoundVars = lists:map(fun({TVar, _}) -> TVar end, bound(T)),
    Mix = lists:zip(BoundVars, Ts),
    Sub = lists:foldr(
        fun({TVar, Concrete}, SAcc)->
        comp(SAcc, maps:put(TVar, Concrete, emptySub()))
        end, emptySub(), Mix),
    {StrippedT, _Ps} = stripbound(T),
    subT(StrippedT, Sub).

-spec can_specialize([{tvar(), [predicate()]}], [hm:type()]) -> boolean().
can_specialize([], []) -> true;
can_specialize([{_TVar, Ps}| Rest], [T| Ts]) ->
    FirstMatch = class_preds_sats(Ps, T),
    RestMatch = can_specialize(Rest, Ts),
    FirstMatch and RestMatch.

class_preds_sats([], T) -> true;
class_preds_sats([{class, Class, _} | Rest], T) ->
    FirstMatch = is_matching_class(Class, T),
    RestOfMatch = class_preds_sats(Rest, T),
    FirstMatch and RestOfMatch.

is_matching_class(Class, Type) ->
    Members = get_all_class_types(rt:defaultClasses(), Class),
    has_matching(Members, Type).

has_matching([], Type) -> false;
has_matching([H| Tail], Type) ->
    case eqType(H, Type) of
        true -> true;
        false -> has_matching(Tail, Type)
    end.

get_all_class_types(Class) ->
    get_all_class_types(rt:defaultClasses(), Class).

get_all_class_types([], Class) -> [];
get_all_class_types([H| Tail], Class) ->
    case H of 
        {class, Class, T} -> [T | get_all_class_types(Tail, Class)];
        _                 -> get_all_class_types(Tail, Class)
    end.
%%%%%%%%%%%%%%%%%%%%
%% Pretty printing
%%%%%%%%%%%%%%%%%%%%
% pretty :: Type -> IO
pretty(T) -> 
    prettify(env:empty(),T),
    ok.

% Stateful pretty printer
prettify(Env, {bt, _, A}) -> io:fwrite("~p", [A]), Env;
prettify(Env, {funt, _, As, B}) ->
    io:fwrite("(", []),
    Env_ = util:interFoldEffect(
        fun(A,E) -> prettify(E,A) end
        , fun() -> io:fwrite(",") end
        , Env, As),
    io:fwrite(")", []),
    io:fwrite("->", []),
    Env__ = prettify(Env_,B),
    Env__;
prettify(Env, {tvar, _, A}) when is_list(A) ->
    io:fwrite("~s", [A]),
    Env;
prettify(Env, {tvar, _, A}) ->
    X = env:lookup(A, Env),
    case X of
        undefined -> 
            L = env:length(Env) + 65,
            io:fwrite("~c", [L]),
            env:extend(A,L,Env);
        _         -> 
            io:fwrite("~c", [X]),
            Env
    end;
prettify(Env, {tcon, _, N, As}) when not is_list(N)->
    Env_ = prettify(Env, N),
    io:fwrite(" "),
    util:interFoldEffect(
    fun(A,E) -> prettify(E,A) end
    , fun() -> io:fwrite(" ") end
    , Env_, As);
prettify(Env, {tcon, _, N, As}) ->
    case N of
        "List" ->
            io:fwrite("["),
            E = util:interFoldEffect(
            fun(A,E) -> prettify(E,A) end
            , fun() -> io:fwrite(" ") end
            , Env, As),
            io:fwrite("]"),E;
        "Tuple" ->
            io:fwrite("{"),
            E = util:interFoldEffect(
            fun(A,E) -> prettify(E,A) end
            , fun() -> io:fwrite(",") end
            , Env, As),
            io:fwrite("}"),E;
        "Union" ->
            io:fwrite("("),
            E = util:interFoldEffect(
            fun(A,E) -> prettify(E,A) end
            , fun() -> io:fwrite("|") end
            , Env, As),
            io:fwrite(")"),E;
        _       -> 
            io:fwrite("~s ", [N]),
            util:interFoldEffect(
            fun(A,E) -> prettify(E,A) end
            , fun() -> io:fwrite(" ") end
            , Env, As)
    end;
prettify(Env,{forall, _, Ps, A}) ->
    case Ps of
        [] -> prettify(Env, A);
        _ ->
            io:fwrite("[",[]),
            Env2 = lists:foldl(fun(P, AccEnv) ->
                case P of
                    {class,C,T_} -> 
                        io:fwrite("~s ",[C]),
                        AccEnv_ = prettify(AccEnv, T_),
                        io:fwrite(";",[]),
                        AccEnv_
                end
            end, Env, Ps),
            io:fwrite("].",[]),
            prettify(Env2, A)
    end;
prettify(Env,{whilst,Ps,A}) ->
    Env1 = lists:foldl(fun(P, AccEnv) ->
        case P of
            {oc,CT,MTs} ->
                AccEnv_ = prettify(AccEnv, CT),
                io:fwrite(" :~~: {",[]),
                AccEnv__ = util:interFoldEffect(
                    fun(MT,AccE) -> prettify(AccE,MT) end
                    ,fun() -> io:fwrite(" || ") end
                , AccEnv_, MTs),
                io:fwrite("} ",[]),
                AccEnv__
        end
    end, Env, Ps),
    prettify(Env1, A);
prettify(Env, {tMeta, L, Id, Tvs, Type, Mono}) ->
    % TODO
    % {tMeta, Id, Tvs, Type, Mono} = get_meta(Env, Id),
    io:fwrite("?",[]),
    case Mono of
        true  -> io:fwrite("`",[]);
        false -> io:fwrite("",[])
    end,

    X = env:lookup(Id, Env),
    Env_ = case X of
        undefined ->
            MC = env:length(Env) + 65,
            io:fwrite("~c~s", [MC, showList(Tvs)]),
            env:extend(Id, MC, Env);
        _         ->
            io:fwrite("~c~s", [X, showList(Tvs)]),
            Env
    end,
    case Type of
        null  -> Env_;
        Valid -> prettify(Env_, Valid)
    end;
prettify(Env, {tSkol, L, Id}) ->
    X = env:lookup(Id, Env),
    case X of
        undefined ->
            MC = env:length(Env) + 97,
            io:fwrite("'~c", [MC]),
            env:extend(Id, MC, Env);
        _         ->
            io:fwrite("'~c", [X]),
            Env
    end;
prettify(Env, NotType) ->
    ?PRINT(NotType),
    Env.

showList([]) -> "";
showList(List) ->
    ListToShow = io_lib:format("~p",[List]),
    lists:flatten(ListToShow).

showAny(Val) ->
    ListToShow = io_lib:format("~p",[Val]),
    lists:flatten(ListToShow).

prettyCs([], S) -> S;
prettyCs([{T1,T2}|Cs],S) -> 
    S_ = prettify(S,T1),
    io:fwrite(" :==: "),
    S__ = prettify(S_,T2),
    io:fwrite("~n"),
    prettyCs(Cs,S__).

%% check types are same irrespective of line number
is_same({bt, _, T1}, {bt, _, T2}) -> T1 == T2;
is_same({funt, _, T1As, T1B}, {funt, _, T2As, T2B}) ->
    % ?PRINT(T1As), ?PRINT(T2As),
    IsParamsMatch = case length(T1As) == length(T2As) of
        true  -> is_same_types(T1As,T2As);
        false -> false
    end,
    IsParamsMatch and is_same(T1B, T2B);
is_same({tvar, _, A1}, {tvar, _, A2}) -> A1 == A2;
is_same({tcon, _, N, A1s}, {tcon, _, N, A2s}) -> is_same_types(A1s, A2s);
is_same({forall, _, P1s, A1},{forall, _, P2s, A2}) ->
    is_same_predicates(P1s, P2s) and is_same(A1, A2);
is_same(T1,{whilst,[],T2}) -> is_same(T1, T2);
is_same({whilst,[],T1}, T2) -> is_same(T1, T2);
is_same({whilst,P1s,A1},{whilst,P2s,A2}) ->
    is_same_predicates(P1s, P2s) and is_same(A1, A2);
is_same({tMeta, _, Id, Tvs, Type1, Mono1}, {tMeta, _, Id, Tvs, Type2, Mono2}) ->
    Mono1 == Mono2 and is_same(Type1, Type2);
is_same({tSkol, _, Id}, {tSkol, _, Id}) -> true;
is_same(T1,T2) -> io:fwrite("Wrong types ~p : ~p ",[T1, T2]), false.

%% helpers
is_same_types(T1s,T2s)->
    not lists:member(false,
            lists:map(fun({T1, T2}) -> is_same(T1, T2) end, lists:zip(T1s,T2s))).

is_same_predicates(P1s,P2s)->
    not lists:member(false, 
            lists:map(fun({P1, P2}) -> P1==P2 end, lists:zip(P1s,P2s))).

%% Sub type relation checker
isSubType({tcon, _, "Union", Ts}, T) ->
    lists:any(fun(X) -> eqType(T, X) end, Ts);
isSubType(T, {tcon, _, "Union", Ts}) ->
    lists:any(fun(X) -> eqType(T, X) end, Ts);
isSubType(T1, T2) -> eqType(T1, T2).

% most_general_type()

%% Type Check Helpers
get_fn_args({funt, _, Args, _}) ->
    Args.
get_fn_rt({funt, _, _, Ret}) ->
    Ret.

% check if the type has any type variable.
% only for forall now, may have to extend.
-spec has_type_var(type()) -> boolean().
has_type_var({forall, _, _, _}) -> true;
has_type_var(_)                 -> false.

-spec type_without_bound(type()) -> type().
type_without_bound(T) ->
    {ST, _} = stripbound(T),
    ST.

% check its a type var or not.
-spec is_type_var(type()) -> boolean().
is_type_var({tvar, _, _}) -> true;
is_type_var(_)            -> false.

freshTSkol(L) -> tSkol(make_ref(), L).

freshTMeta(Env, Tvs, Mono, L) ->
    Ref = make_ref(),
    TM = tMeta(Ref, Tvs, Mono, L),
    Env_ = env:set_meta(Env, Ref, TM),
    {Env_, TM}.
freshTMeta(Env, Tvs, L) -> freshTMeta(Env, Tvs, false, L).

getAllTMeta ({bt, _, _}) -> [];
getAllTMeta ({funt, _, Args, Ret}) ->
    ArgTMs = lists:foldr(fun(Arg, TMs) ->
        TMs ++ getAllTMeta(Arg)
    end,
    [] ,Args),
    RetTM = getAllTMeta(Ret),
    ArgTMs ++ RetTM;
getAllTMeta ({tvar, _, _}) -> [];
getAllTMeta ({tcon, _, _, Args}) ->
    lists:foldr(fun(Arg, TMs) ->
        TMs ++ getAllTMeta(Arg)
    end,
    [] ,Args);
getAllTMeta ({forall, {tvar, _, _}, _, A}) -> getAllTMeta(A);
getAllTMeta ({whilst, _, T}) -> getAllTMeta(T);
getAllTMeta ({tMeta, _, _, _, _, _} = TM) -> [TM];
getAllTMeta ({tSkol, _, _}) -> [];
getAllTMeta (NotSupported) -> ?PRINT(NotSupported), [].

replaceTMeta(X, S, {tvar, _, _} = TVar) -> TVar;
replaceTMeta({tMeta, _ , _Id, _Tvs, Type, _}, S, {tMeta, _ , _Id, _Tvs, Type, _}) ->
    S;
replaceTMeta(X, S, {funt, L, Args, RetTy}) ->
    SubArgs = lists:map(fun (A) -> replaceTMeta(X, S, A) end, Args),
    hm:funt(SubArgs, replaceTMeta(X, S, RetTy), L);
replaceTMeta(X, S, {tcon, L, Name, Args}) ->
    SubArgs = lists:map(fun (A) -> replaceTMeta(X, S, A) end, Args),
    hm:tcon(replaceTMeta(X, S, Name), SubArgs, L);
replaceTMeta(X, S, {forall, Name, Ps, Body}) ->
    {forall, Name, Ps, replaceTMeta(X, S, Body)};
replaceTMeta(_X, _S, T) -> T.

replaceFreshTMeta(Env, Type) ->
    AllTMs = getAllTMeta(Type),
    NO_Dup_TMS = lists:usort(AllTMs), %% hack to avoid duplicate use set instead of list
    lists:foldr(fun({tMeta, L, _, [], _, Mono} = TM, {Ei, Tp}) ->
        {Ei_, NM} = hm:freshTMeta(Ei, [], Mono, L),
        TP_ = replaceTMeta(TM, NM, Tp),
        {Ei_, TP_}
    end,
    {Env, Type}, NO_Dup_TMS).

generalizeType (Type) ->
    AllTMs = lists:usort(getAllTMeta(Type)),
    generalizeTMeta(AllTMs, Type).

generalizeTMeta ([], T) -> T;
generalizeTMeta ([TM|TMs], T) -> {forall, {tvar,getLn(T), TM}, [], generalizeTMeta(TMs, T)}.

getListType(_Env, {tcon, _, "List", [LType]}) ->
    LType;
getListType(Env, {tMeta, _ , Id_m, _, _, _}=TM) ->
    {tMeta, _, Id_m, _, Type, _} = env:get_meta(Env, Id_m),
    getListType(Env, Type);
getListType(_Env, _Type) ->
    erlang:error({type_error, "Not a valid list type"}).

metaTupleTypeOfN(Env, N, L)->
    {Env_, TTs } =lists:foldr(fun(_C, {Ei, TMs}) ->
        {Ei_, NM} = hm:freshTMeta(Ei, [], false, L),
        {Ei_, TMs ++ [NM]}
    end, {Env, []}, lists:seq(1, N)),
    TupleType = hm:tcon("Tuple", TTs, L),
    {Env_, TupleType}.

getTupleType(_Env, {tcon, _, "Tuple", TTys}) ->
    TTys;
getTupleType(Env, {tMeta, _ , Id_m, _, _, _}=TM) ->
    {tMeta, _, Id_m, _, Type, _} = env:get_meta(Env, Id_m),
    getListType(Env, Type);
getTupleType(_Env, _Type) ->
    erlang:error({type_error, "Not a valid tuple type"}).

generalizeSpecT (Type,Env) ->
    MonoVars = free(Type),
    BoundInEnv = env:freeInEnv(Env),
    Generalizable = sets:subtract(MonoVars, BoundInEnv),
    bindTV(sets:to_list(Generalizable),Type).

% bind generalized variables
bindTV ([],T)      -> T;
bindTV ([X|Xs],T)  -> {forall, {tvar,getLn(T), X}, [], bindTV(Xs,T)}.