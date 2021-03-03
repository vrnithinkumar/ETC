-module(bdd_hm).

-export([tests/0, tests_full_infer/0]).

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
% tMeta(Id, Tvs, Type, Mono) -> {tMeta, Id, Tvs, Type, Mono}.
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
showType({tSkol, Id}) -> Id;
showType(Ty) -> io_lib:format("Unknown type: ~p",[Ty]).

showTerm({var, Name}) -> Name;
showTerm({abs, Name, Body}) -> "(\\" ++ Name ++ "." ++ showTerm(Body) ++ ")";
showTerm({app, Left, Right}) ->
    "(" ++ showTerm(Left) ++ " " ++ showTerm(Right) ++ ")";
showTerm({ann, Term, Type}) -> 
    "(" ++ showTerm(Term) ++ " : " ++ showType(Type) ++ ")";
showTerm(Term) -> io_lib:format("Unknown term: ~p",[Term]).

prune({tMeta, _Id, _Tvs, Type, _Mono}) when Type /= null ->
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

substTVar(X, S, {tVar, Name}) when Name == X -> S;
substTVar(X, S, {tMeta, _Id, _Tvs, Type, _}) when Type /= null ->
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
checkSolution({tMeta, _, Tvs_m, _, _} = M, {tMeta, _, Tvs_t, Type_t, _}) ->
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
unify(Tvs, A , {tMeta, _, _, _, _} = B) ->
    unifyTMeta(Tvs, B, A);
unify(_Tvs, A, B) ->
    terr("unify failed: " ++ showType(A) ++ " :-: " ++ showType(B)).


unifyTMeta(_Tvs, M, M) -> no_return;
unifyTMeta(Tvs, {tMeta, _, _, Type, _}, T) when Type /= null ->
    unify(Tvs, Type, T);
unifyTMeta(Tvs, M, {tMeta, _, _, Type, _}) when Type /= null ->
    unifyTMeta(Tvs, M, Type);
unifyTMeta(Tvs, {tMeta, Id, Tvs, _, Mono}=M, T) ->
    case checkSolution(M, T) of
        true  -> {tMeta, Id, Tvs, T, Mono};
        false -> 
            terr("unifyTMeta failed: " ++ showType(M) ++ ":=" ++ showType(T))
end.

subsume(Tvs, A, {tForall, _, _}=B) -> 
    Sk = freshTSkol(),
    {tSkol, SkId} = Sk,
    unify([SkId] ++ Tvs, A, openTForall(B, Sk));
subsume(Tvs, {tForall, _, _}=A, B) ->
    M = freshTMeta(Tvs),
    unify(Tvs, openTForall(A, M), B);
subsume(Tvs, A, B) -> unify(Tvs, A, B).

% Inference/ Synthesis
synth(Env, _Tvs, {var, Name}) ->
    case maps:get(Name, Env, not_found) of 
        not_found -> terr("undefined var : " ++  Name);
        Ty -> Ty
    end;
synth(Env, Tvs, {ann, Term, Type}) ->
    check(Env, Tvs, Term, Type),
    Type;
synth(Env, Tvs, {app, _Left, _Right}=Term) ->
    {FT, As} = flattenApp(Term),
    Ty = synth(Env, Tvs, FT),
    synthapps(Env, Tvs, Ty, As, null, []);
synth(Env, Tvs, {abs, Name, Body}) ->
    A = freshTMeta(Tvs, true),
    B = freshTMeta(Tvs),
    check(maps:put(Name, A, Env), Tvs, Body, B),
    tFun(A, B);
synth(_, _, Term) ->
    terr("cannot synth : " ++ showTerm(Term)).

synthapps(Env, Tvs, {tForall, _, _} = Ty, As, Ety, Acc) ->
    M = freshTMeta(Tvs),
    synthapps(Env, Tvs, openTForall(Ty, M), As, Ety, Acc);
synthapps(Env, Tvs, {tFun, Left, Right}, As, Ety, Acc) when length(As) > 0 ->
    [TM | AsTail] = As,
    Acc_ = Acc ++ [{TM, Left}],
    synthapps(Env, Tvs, Right, AsTail, Ety, Acc_);
synthapps(Env, Tvs, {tMeta, _Id, Tvs_m, Type, _}, As, Ety, Acc) when length(As) > 0 ->
    case Type of
        null  -> 
        A = freshTMeta(Tvs_m),
        B = freshTMeta(Tvs_m),
        % ty.type = TFun(a, b),
        %  BUG: Potential
        Ty_Type = tFun(A, B),
        [TM | AsTail] = As,
        Acc_ = Acc ++ [{TM, A}],
        synthapps(Env, Tvs, B, AsTail, Ety, Acc_);
        Valid -> synthapps(Env, Tvs, Valid, As, Ety, Acc)
    end;
synthapps(_, _, Ty, As, _, _) when length(As) > 0 ->
    terr("synthapps failed, not a function type: " ++ showType(Ty));
synthapps(Env, Tvs, Ty, _As, Ety, Acc) ->
    case Ety of
        null    -> pickAndCheckArgs(Env, Tvs, Acc);
        NotNull -> unify(Tvs, Ty, NotNull)
    end,
    Ty.

% Bug to check
pickAndCheckArgs(_, _, []) -> done;
pickAndCheckArgs(Env, Tvs, Acc) ->
    {{Tm, TmTy}, RestAcc} = pickArg(Acc),
    check(Env, Tvs, Tm, TmTy),
    pickAndCheckArgs(Env, Tvs, RestAcc).

% Bug to check
pickArg(Acc) -> pickArg_(Acc, []).
pickArg_(Acc_Done, []) ->
    % Nothing match return shift
    {hd(Acc_Done), tl(Acc_Done)};
pickArg_(Acc_Done, [{F,S} | Acc_Rem]) ->
    case S of
        {tMeta, _, _, _, _} ->
            {{F,S}, Acc_Done ++ Acc_Rem};
        _ -> pickArg_(Acc_Done ++ [{F,S}], Acc_Rem)
    end.

check(Env, Tvs, Term, {tMeta, _, _, Type, _}) when Type /= null->
    check(Env, Tvs, Term, Type);
check(Env, Tvs, Term, {tForall, _, _} = Ty) ->
    Sk = freshTSkol(),
    {tSkol, SkId} = Sk,
    check(Env, [SkId] ++ Tvs, Term, openTForall(Ty, Sk));
check(Env, Tvs, {abs, Name, Body}, {tFun, Left, Right}) ->
    check(maps:put(Name, Left, Env), Tvs, Body, Right);
check(Env, Tvs, {app, _, _} = Term, Ty) ->
    {FT, As} = flattenApp(Term),
    FTy = synth(Env, Tvs, FT),
    synthapps(Env, Tvs, FTy, As, Ty, []);
check(Env, Tvs, Term, Ty) ->
    Inf  = synth(Env, Tvs, Term),
    subsume(Tvs, Inf, Ty).

infer(Env, Term) ->
    % resetTMetaId();
    % resetTSkolId();
    Ty = synth(Env, [], Term),
    prune(Ty).

%% ------------- Tests ------------%%
% Helpers for testing
v(N) -> var(N).
tv(N) -> tVar(N).
tid() -> tForall("t", tFun(tv("t"), tv("t"))).
listT(T) -> tApp(tv("List"), T).
st(S, T) -> tApp(tApp(tv("ST"), S), T).
pair(A, B) -> tApp(tApp(tv("Pair"), A), B).

env() -> #{
  "head" => tForall("t", tFun(listT(tv("t")), tv("t"))),
  "tail" => tForall("t", tFun(listT(tv("t")), listT(tv("t")))),
  "Nil" => tForall("t", listT(tv("t"))),
  "Cons" => tForall("t", tFun(tv("t"), tFun(listT(tv("t")), listT(tv("t"))))),
  "single" => tForall("t", tFun(tv("t"), listT(tv("t")))),
  "append" => tForall("t", tFun(listT(tv("t")), tFun(listT(tv("t")), listT(tv("t"))))),
  "length" => tForall("t", tFun(listT(tv("t")), tv("Int"))),
  "runST" => tForall("t", tFun(tForall("s", st(tv("s"), tv("t"))), tv("t"))),
  "argST" => tForall("s", st(tv("s"), tv("Int"))),
  "pair" => tForall("a", tForall("b", tFun(tv("a"), tFun(tv("b"), pair(tv("a"), tv("b")))))),
  "pair2" => tForall("b", tForall("a", tFun(tv("a"), tFun(tv("b"), pair(tv("a"), tv("b")))))),
  "id" => tid(),
  "ids" => listT(tid()),
  "inc" => tFun(tv("Int"), tv("Int")),
  "choose" => tForall("t", tFun(tv("t"), tFun(tv("t"), tv("t")))),
  "poly" => tFun(tid(), pair(tv("Int"), tv("Bool"))),
  "auto" => tFun(tid(), tid()),
  "auto2" => tForall("b", tFun(tid(), tFun(tv("b"), tv("b")))),
  "map" => tForall("a", tForall("b", tFun(tFun(tv("a"), tv("b")), tFun(listT(tv("a")), listT(tv("b")))))),
  "app" => tForall("a", tForall("b", tFun(tFun(tv("a"), tv("b")), tFun(tv("a"), tv("b"))))),
  "revapp" => tForall("a", tForall("b", tFun(tv("a"), tFun(tFun(tv("a"), tv("b")), tv("b"))))),
  "f" => tForall("t", tFun(tFun(tv("t"), tv("t")), tFun(listT(tv("t")), tv("t")))),
  "g" => tForall("t", tFun(listT(tv("t")), tFun(listT(tv("t")), tv("t")))),
  "k" => tForall("t", tFun(tv("t"), tFun(listT(tv("t")), tv("t")))),
  "h" => tFun(tv("Int"), tid()),
  "l" => listT(tForall("t", tFun(tv("Int"), tFun(tv("t"), tv("t"))))),
  "r" => tFun(tForall("a", tFun(tv("a"), tid())), tv("Int"))
}.

test_cases() -> [
  %    A
  abs("x", abs("y", v("x"))),
  app(v("choose"), v("id")),
  ann(app(v("choose"), v("id")), tFun(tid(), tid())),
  app(app(v("choose"), v("Nil")), v("ids")),
  app(v("id"), v("auto")),
  app(v("id"), v("auto2")),
  app(app(v("choose"), v("id")), v("auto")),
  app(app(v("choose"), v("id")), v("auto2")), % X
  app(app(v("f"), app(v("choose"), v("id"))), v("ids")), % X
  app(app(v("f"), ann(app(v("choose"), v("id")), tFun(tid(), tid()))), v("ids")),
  app(v("poly"), v("id")),
  app(v("poly"), abs("x", v("x"))),
  app(app(v("id"), v("poly")), abs("x", v("x"))),

  %% B

  %% C
  app(v("length"), v("ids")),
  app(v("tail"), v("ids")),
  app(v("head"), v("ids")),
  app(v("single"), v("id")),
  ann(app(v("single"), v("id")), listT(tid())),
  app(app(v("Cons"), v("id")), v("ids")),
  app(app(v("Cons"), abs("x", v("x"))), v("ids")),
  app(app(v("append"), app(v("single"), v("inc"))), app(v("single"), v("id"))),
  app(app(v("g"), app(v("single"), v("id"))), v("ids")), %% X
  app(app(v("g"), ann(app(v("single"), v("id")), listT(tid()))), v("ids")),
  app(app(v("map"), v("poly")), app(v("single"), v("id"))),
  app(app(v("map"), v("head")), app(v("single"), v("ids"))),

  %% D
  app(app(v("app"), v("poly")), v("id")),
  app(app(v("revapp"), v("id")), v("poly")),
  app(v("runST"), v("argST")),
  app(app(v("app"), v("runST")), v("argST")),
  app(app(v("revapp"), v("argST")), v("runST")),

  %% E
  app(app(v("k"), v("h")), v("l")), %% X
  app(app(v("k"), abs("x", app(v("h"), v("x")))), v("l")),
  app(v("r"), abs("x", abs("y", v("y"))))
].

tests() ->
    IDType = tForall("t", tFun(tVar("t"), tVar("t"))),
    VAR_ = var("X"),
    ID_ABS = abs("X", VAR_),
    APP_ = app(ID_ABS, VAR_),
    ANN_ = ann(ID_ABS, IDType),
    lists:map(fun(Term) -> showTerm(Term) end, [VAR_, ID_ABS, APP_, ANN_]),
    ok.

tests_full_infer() ->
    % Test = maps:get(env(), "x", undefined),
    % ?PRINT(Test)
    Term = abs("x", abs("y", v("x"))),
    Ty = infer(env(), Term),
    Res = showTerm(Term) ++ showType(Ty),
    io:fwrite("Type Res: ~p ~n",[Res]).