-module(bdd_hm).

-export([tests/0]).

% convert the js code in erlang

%% PRINT Debugging macro%%
-ifndef(PRINT).
-define(PRINT(Var), io:format("DEBUG: ~p:~p - ~p~n~n ~p~n~n", [?MODULE, ?LINE, ??Var, Var])).
-endif.

% Terms
var(Name)        -> {var, Name}.
abs(Name, Body)  -> {abs, Name, Body}.
app(Left, Right) -> {app, Left, Right}.
ann(Term, Type)  -> {ann, Term, Type}.

% Types
tVar(Name)                 -> {tVar, Name}.
tForall(Name, Body)        -> {tForall, Name, Body}.
tFun(Left, Right)          -> {tFun, Left, Right}.
tApp(Left, Right)          -> {tApp, Left, Right}.
tMeta(Id, Tvs, Mono)       -> {tMeta, Id, Tvs, null, Mono}.
tMeta(Id, Tvs, Type, Mono) -> {tMeta, Id, Tvs, Type, Mono}.
tSkol(Id)                  -> {tSkol, Id}.

terr(Reason) -> erlang:error("Type Error: " ++ Reason).

showList(List) ->
    ListToShow = io_lib:format("~p",[List]),
    ListToShow.

% const resetTSkolId = () => { _tskolid = 0 };
freshTSkol() -> tSkol(make_ref()).

freshTMeta(Tvs, Mono) -> tMeta(make_ref(), Tvs, Mono).
freshTMeta(Tvs) -> freshTMeta(Tvs, false).

subset([A|As], B) ->
    case lists:member(B, A) of
        true  -> subset(As, B);
        false -> false
    end;
subset (_A, _B) -> true.

showType({tVar, Name}) -> Name;
showType({tMeta, Id, Tvs, Type, Mono}) ->
    MonoStr = case Mono of
        true  -> "`";
        false -> ""
    end,
    TypeStr = case Type of
        null  -> "";
        Valid -> showType(Valid)
    end,
    "?" ++ MonoStr ++ Id ++ showList(Tvs) ++ TypeStr;
showType({tForall, Name, Body}) ->
    "(forall " ++ Name ++ ". " ++ showType(Body) ++ ")";
showType({tFun, Left, Right}) ->
    "(" ++ showType(Left) ++ " -> " ++ showType(Right) ++ ")";
showType({tApp, Left, Right}) ->
    "(" ++ showType(Left) ++ " " ++ showType(Right) ++ ")";
showType({tSkol, Id}) -> Id.

showTerm({var, Name}) -> Name;
showTerm({abs, Name, Body}) -> "(\\" ++ Name ++ "." ++ showTerm(Body) ++ ")";
showTerm({app, Left, Right}) ->
    "(" ++ showTerm(Left) ++ " " ++ showTerm(Right) ++ ")";
showTerm({ann, Term, Type}) -> 
    "(" ++ showTerm(Term) ++ " : " ++ showType(Type) ++ ")".

prune({tMeta, Id, Tvs, Type, Mono}) when Type /= null ->
    prune(Type);
    % {tMeta, Id, Tvs, prune(Type), Mono};
prune({tFun, Left, Right}) -> tFun(prune(Left), prune(Right));
prune({tApp, Left, Right}) -> tApp(prune(Left), prune(Right));
prune({tForall, Name, Body}) -> tForall(Name, prune(Body));
prune(T) -> T.

flattenApp({app, Left, Right}) ->
    {T, Args} = flattenApp (Left),
    {T, Args ++ [Right]};
    % {T, [Right] ++ Args};
flattenApp(T) -> {T, []}.

substTVar(X, S, {tVar, Name}=T) when Name == X -> S;
substTVar(X, S, {tMeta, Id, Tvs, Type, Mono}) when Type /= null ->
    substTVar(X, S, Type);
substTVar(X, S, {tFun, Left, Right}) ->
    tFun(substTVar(X, S, Left), substTVar(X, S, Right));
substTVar(X, S, {tApp, Left, Right}) ->
    tApp(substTVar(X, S, Left), substTVar(X, S, Right));
substTVar(X, S, {tForall, Name, Body}) when Name /= X ->
    tForall(Name, substTVar(X, S, Body));
substTVar(_X, _S, T) -> T.

openTForall({tForall, Name, Body}, T) -> substTVar(Name, T, Body).

% Subtyping
checkSolution(T, T) -> false;
checkSolution({tMeta, Id_m, Tvs_m, Type_m, Mono_m} = M, {tMeta, Id_t, Tvs_t, Type_t, Mono_t} = T) ->
% todo     if (m.mono) t.mono = true;
    case Type_t of
        null -> checkSolution(M, Type_t);
        _    -> subset(Tvs_m, Tvs_t)
    end;
checkSolution(M, {tFun, Left, Right}) ->
    checkSolution(M, Left) and checkSolution(M, Right);
checkSolution(M, {tApp, Left, Right}) ->
    checkSolution(M, Left) and checkSolution(M, Right);
checkSolution({tMeta, _, _, _, Mono} = M, {tForall, _, Body}) ->
    case Mono of
        true -> false;
        false -> checkSolution(M, Body)
    end;
checkSolution({tMeta, _, Tvs, _, _}, {tSkol, Id}) ->
    lists:member(Id, Tvs);
checkSolution(_M, _T) -> true.

unify(_Tvs, A, A) -> no_return;
unify(_Tvs, {tVar, Name_A}, {tVar, Name_B}) when Name_A == Name_B ->
    no_return;
unify(Tvs, {tFun, Left_A, Right_A}, {tFun, Left_B, Right_B}) ->
    unify(Tvs, Left_A, Left_B),
    unify(Tvs, Right_A, Right_B),
    no_return;
unify(Tvs, {tApp, Left_A, Right_A}, {tApp, Left_B, Right_B}) ->
    unify(Tvs, Left_A, Left_B),
    unify(Tvs, Right_A, Right_B),
    no_return;
unify(Tvs, {tForall, Name_A, Body_A}=A, {tForall, Name_A, Body_A}=B) ->
    Sk = freshTSkol(),
    {tSkol, SkId} = Sk,
    unify([SkId] ++ Tvs, openTForall(A, Sk), openTForall(B, Sk)),
    no_return;
unify(Tvs, {tMeta, _, _, _, _} = A , B) ->
    unifyTMeta(Tvs, A, B);
unify(Tvs, {tMeta, _, _, _, _} = A , B) ->
    unifyTMeta(Tvs, B, A);
unify(Tvs, A, B) ->
    terr("unify failed: " ++ showType(A) ++ " :-: " ++ showType(B)).


unifyTMeta(_Tvs, M, M) -> no_return;
unifyTMeta(Tvs, {tMeta, _, _, Type, _}, T) ->
    unify(Tvs, Type, T);
unifyTMeta(Tvs, {tMeta, _, _, _, _}=M, {tMeta, _, _, Type, _} = T) ->
    unifyTMeta(Tvs, M, Type);
unifyTMeta(Tvs, {tMeta, Id, Tvs, _, Mono}=M, T) ->
    case checkSolution(M, T) of
        true  -> {tMeta, Id, Tvs, T, Mono};
        false -> 
            terr("unifyTMeta failed: " ++ showType(M) ++ ":=" ++ showType(T))
end.

subsume(Tvs, A, {tForall, Name_A, Body_A}=B) -> 
    Sk = freshTSkol(),
    {tSkol, SkId} = Sk,
    unify([SkId] ++ Tvs, A, openTForall(B, Sk));
subsume(Tvs, {tForall, Name_A, Body_A}=A, B) ->
    M = freshTMeta(Tvs),
    unify(Tvs, openTForall(A, M), B);
subsume(Tvs, A, B) -> unify(Tvs, A, B).

% Inference/ Synthesis
synth(Env, Tvs, {var, Name}) ->
    case maps:get(Env, Name, not_found) of 
        not_found -> terr("undefined var : " ++  Name);
        Ty -> Ty
    end;
synth(Env, Tvs, {ann, Term, Type}) ->
    check(Env, Tvs, Term, Type),
    Type;
synth(Env, Tvs, {app, Left, Right}=Term) ->
    {FT, As} = flattenApp(Term),
    Ty = synth(Env, Tvs, FT),
    synthapps(Env, Tvs, Ty, As);
synth(Env, Tvs, {abs, Name, Body}=Term) ->
    A = freshTMeta(Tvs, true),
    B = freshTMeta(Tvs),
    check(maps:insert(Name, A, Env), Tvs, Body, B),
    tFun(A, B);
synth(_, _, Term) ->
    terr("cannot synth : " ++ showTerm(Term)).

synthapps(Env, Tvs, Ty, As) -> ok.
synthapps(Env, Tvs, Ty, As, Ety) -> ok.
synthapps(Env, Tvs, Ty, As, Ety, Acc) -> ok.

check(Env, Tvs, Term, {tMeta, _, _, Type, _}) when Type /= null->
    check(Env, Tvs, Term, Type);
check(Env, Tvs, Term, {tForall, _, _} = Ty) ->
    Sk = freshTSkol(),
    {tSkol, SkId} = Sk,
    check(Env, [SkId] ++ Tvs, Term, openTForall(Ty, Sk));
check(Env, Tvs, {abs, Name, Body}, {tFun, Left, Right}) ->
    check(maps:insert(Name, Left, Env), Tvs, Body, Right);
check(Env, Tvs, {app, _, _} = Term, Ty) ->
    {FT, As} = flattenApp(Term),
    FTy = synth(Env, Tvs, FT),
    synthapps(Env, Tvs, FTy, As, Ty);
check(Env, Tvs, Term, Ty) ->
    Inf  = synth(Env, Tvs, Term),
    subsume(Tvs, Inf, Ty).

tests() ->
    IDType = tForall("t", tFun(tVar("t"), tVar("t"))),
    VAR_ = var("X"),
    ID_ABS = abs("X", VAR_),
    APP_ = app(ID_ABS, VAR_),
    ANN_ = ann(ID_ABS, IDType),
    lists:map(fun(Term) -> showTerm(Term) end, [VAR_, ID_ABS, APP_, ANN_])
    .