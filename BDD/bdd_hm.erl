-module(bdd_hm).

-export([tests/0, tests_full_infer/0, all_tests/0]).

% convert the js code in erlang

%% PRINT Debugging macro%%
-ifndef(PRINT).
-define(PRINT(Var), io:format("DEBUG: ~p:~p - ~p~n~n ~p~n~n", [?MODULE, ?LINE, ??Var, Var])).
-endif.
% Environment
% Type checker Environment
-record(ten, 
{
    bindings = #{},
    metaMap  = #{}
}).

get_binding(Env, X) -> 
    maps:get(X, Env#ten.bindings, not_found).
set_binding(Env, X, Type) ->
    Env#ten{bindings = maps:put(X, Type, Env#ten.bindings)}.
get_meta(Env, Id) -> 
    maps:get(Id, Env#ten.metaMap, not_found).
set_meta(Env, Id, Type) ->
    Env#ten{metaMap = maps:put(Id, Type, Env#ten.metaMap)}.

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

showList([]) -> "";
showList(List) ->
    ListToShow = io_lib:format("~p",[List]),
    lists:flatten(ListToShow).

showAny(Val) ->
    ListToShow = io_lib:format("~p",[Val]),
    lists:flatten(ListToShow).

intToChar(Val) ->
    L = Val + 65,
    io_lib:format("~c", [L]).

intToSmallChar(Val) ->
    L = Val + 97,
    io_lib:format("~c", [L]).

% const resetTSkolId = () => { _tskolid = 0 };
freshTSkol() -> tSkol(make_ref()).

freshTMeta(Env, Tvs, Mono) ->
    Ref = make_ref(),
    TM = tMeta(Ref, Tvs, Mono),
    Env_ = set_meta(Env, Ref, TM),
    {Env_, TM}.
freshTMeta(Env, Tvs) -> freshTMeta(Env, Tvs, false).

subset([A|As], B) ->
    case lists:member(B, A) of
        true  -> subset(As, B);
        false -> false
    end;
subset (_A, _B) -> true.

-record(meta,
{
    metaCount = 0,
    skolCount = 0,
    skolMap = #{},
    metaMap  = #{}
}).

init_meta() -> #meta{}.

mapAndNext(MetaState, Ref) ->
    MM = MetaState#meta.metaMap,
    case maps:get(Ref, MM, not_found) of
        not_found ->
            MC = MetaState#meta.metaCount,
            {
                intToChar(MC),
                MetaState#meta{ metaCount = MC+1, metaMap = maps:put(Ref, MC, MM)}
            };
        Found -> {intToChar(Found), MetaState}
    end.

mapAndNextSkol(MetaState, Ref) ->
    SM = MetaState#meta.skolMap,
    case maps:get(Ref, SM, not_found) of
        not_found ->
            SC = MetaState#meta.skolCount,
            {
                intToSmallChar(SC),
                MetaState#meta{ skolCount = SC+1, skolMap = maps:put(Ref, SC, SM)}
            };
        Found -> {intToSmallChar(Found), MetaState}
    end.

showType(Ty) ->
    {TyStr, _} = showType_(Ty, init_meta()),
    TyStr.

showType_({tVar, Name}, State) -> {Name, State};
showType_({tMeta, Id, Tvs, Type, Mono}, State) ->
    % TODO
    % {tMeta, Id, Tvs, Type, Mono} = get_meta(Env, Id),
    MonoStr = case Mono of
        true  -> "`";
        false -> ""
    end,
    {TypeStr, State_} = case Type of
        null  -> {"", State};
        Valid -> showType_(Valid, State)
    end,
    {IdStr, State__} = mapAndNext(State_, Id),
    {"?" ++ MonoStr ++ IdStr ++ showList(Tvs) ++ TypeStr, State__};
showType_({tForall, Name, Body}, State) ->
    {BdStr, State_} = showType_(Body, State),
    {"(forall " ++ Name ++ ". " ++ BdStr ++ ")", State_};
showType_({tFun, Left, Right}, State) ->
    {LStr, State_} = showType_(Left, State),
    {RStr, State__} = showType_(Right, State_),
    {"(" ++ LStr ++ " -> " ++ RStr ++ ")", State__};
showType_({tApp, Left, Right}, State) ->
    {LStr, State_} = showType_(Left, State),
    {RStr, State__} = showType_(Right, State_),
    {"(" ++ LStr ++ " " ++ RStr ++ ")", State__};
showType_({tSkol, Id}, State) ->
    {IdStr, State_} = mapAndNextSkol(State, Id),
    {"'" ++ IdStr, State_};
showType_(Ty, _) -> io_lib:format("Unknown type: ~p", [Ty]).

showTerm({var, Name}) -> Name;
showTerm({abs, Name, Body}) -> "(\\" ++ Name ++ "." ++ showTerm(Body) ++ ")";
showTerm({app, Left, Right}) ->
    "(" ++ showTerm(Left) ++ " " ++ showTerm(Right) ++ ")";
showTerm({ann, Term, Type}) -> 
    "(" ++ showTerm(Term) ++ " : " ++ showType(Type) ++ ")";
showTerm(Term) -> io_lib:format("Unknown term: ~p",[Term]).

%% prune can modify the state of tMeta type.
%% So passing Env to track.
prune(Env, {tMeta, Id_m, _, _, _}) ->
    {tMeta, Id_m, Tvs, Type, Mono} = get_meta(Env, Id_m),
    case Type of 
        null -> {Env, {tMeta, Id_m, Tvs, Type, Mono}};
        Valid ->
            {Env_1, PT} = prune(Env, Valid),
            UpdatedMeta = {tMeta, Id_m, Tvs, PT, Mono},
            Env_2 = set_meta(Env_1, Id_m, UpdatedMeta),
            {Env_2, PT}
            % {Env_2, UpdatedMeta}
    end;
prune(Env, {tFun, Left, Right}) ->
    {Env_L, PT_L} = prune(Env, Left),
    {Env_R, PT_R} = prune(Env_L, Right),
    {Env_R, tFun(PT_L, PT_R)};
prune(Env, {tApp, Left, Right}) ->
    {Env_L, PT_L} = prune(Env, Left),
    {Env_R, PT_R} = prune(Env_L, Right),
    {Env_R, tApp(PT_L, PT_R)};
prune(Env, {tForall, Name, Body}) ->
    {Env_, PT} = prune(Env, Body),
    {Env_, tForall(Name, PT)};
prune(Env, T) -> {Env, T}.

applyEnv(Env, {tMeta, Id, _, _, _}) ->
    get_meta(Env, Id);
applyEnv(Env, {tFun, Left, Right}) -> 
    tFun(applyEnv(Env, Left), applyEnv(Env, Right));
applyEnv(Env, {tApp, Left, Right}) -> 
    tApp(applyEnv(Env, Left), applyEnv(Env, Right));
applyEnv(Env, {tForall, Name, Body}) -> 
    tForall(Name, applyEnv(Env, Body));
applyEnv(_, T) -> T.

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
checkSolution(Env, T, T) -> {Env, false};
checkSolution(Env, {tMeta, Id_m, _, _, _} = M, {tMeta, Id_t, _, _, _}) ->
% todo     if (m.mono) t.mono = true;
    {tMeta, Id_m, Tvs_m, _, Mono_m} = get_meta(Env, Id_m),
    {tMeta, Id_t, Tvs_t, Type_t, _} = get_meta(Env, Id_t),
    Env_ = case Mono_m of
        true -> set_meta(Env, Id_t, {tMeta, Id_t, Tvs_t, Type_t, true});
        false -> Env
    end,
    case Type_t of
        null -> checkSolution(Env_, M, Type_t);
        _    -> {Env_, subset(Tvs_m, Tvs_t)}
    end;
checkSolution(Env, M, {tFun, Left, Right}) ->
    {Env_, LRes} = checkSolution(Env, M, Left),
    {Env__, RRes} = checkSolution(Env_, M, Right),
    {Env__, LRes and RRes};
checkSolution(Env, M, {tApp, Left, Right}) ->
    {Env_, LRes} = checkSolution(Env, M, Left),
    {Env__, RRes} = checkSolution(Env_, M, Right),
    {Env__, LRes and RRes};
checkSolution(Env, {tMeta, Id_m, _, _, _} = M, {tForall, _, Body}) ->
    {tMeta, Id_m, _, _, Mono} = get_meta(Env, Id_m),
    case Mono of
        true -> {Env, false};
        false -> checkSolution(Env, M, Body)
    end;
checkSolution(Env, {tMeta, Id_m, _, _, _}, {tSkol, Id}) ->
    {tMeta, Id_m, Tvs, _, _} = get_meta(Env, Id_m),
    {Env, lists:member(Id, Tvs)};
checkSolution(Env, _M, _T) -> {Env, true}.

unify(Env, _Tvs, A, A) -> {Env, A};
unify(Env, _Tvs, {tVar, Name_A}, {tVar, Name_B}) when Name_A == Name_B ->
    {Env, {tVar, Name_A}};
unify(Env, Tvs, {tFun, Left_A, Right_A}, {tFun, Left_B, Right_B}) ->
    {Env_, Left_U} = unify(Env, Tvs, Left_A, Left_B),
    {Env__, Right_U} = unify(Env_, Tvs, Right_A, Right_B),
    {Env__, {tFun, Left_U, Right_U}};
unify(Env, Tvs, {tApp, Left_A, Right_A}, {tApp, Left_B, Right_B}) ->
    {Env_, Left_U} = unify(Env, Tvs, Left_A, Left_B),
    {Env__, Right_U} = unify(Env_, Tvs, Right_A, Right_B),
    {Env__, {tApp, Left_U, Right_U}};
unify(Env, Tvs, {tForall, Name_A, Body_A}=A, {tForall, Name_A, Body_A}=B) ->
    Sk = freshTSkol(),
    {tSkol, SkId} = Sk,
    unify(Env, [SkId] ++ Tvs, openTForall(A, Sk), openTForall(B, Sk));
unify(Env, Tvs, {tMeta, Id_m, _, _, _}, B) ->
    A = get_meta(Env, Id_m),
    unifyTMeta(Env, Tvs, A, B);
unify(Env, Tvs, A , {tMeta, Id_m, _, _, _}) ->
    B = get_meta(Env, Id_m),
    unifyTMeta(Env, Tvs, B, A);
unify(_Env, _Tvs, A, B) ->
    terr("unify failed: " ++ showType(A) ++ " :-: " ++ showType(B)).


unifyTMeta(Env, _Tvs, M, M) -> {Env, M};
unifyTMeta(Env, Tvs, {tMeta, _, _, Type, _}, T) when Type /= null ->
    unify(Env, Tvs, Type, T);
unifyTMeta(Env, Tvs, M, {tMeta, _, _, Type, _}) when Type /= null ->
    unifyTMeta(Env, Tvs, M, Type);
unifyTMeta(Env, Tvs, {tMeta, Id, _, _, Mono}=M, T) ->
    {Env_, Res} = checkSolution(Env, M, T),
    case Res of
        true  ->
            TM = {tMeta, Id, Tvs, T, Mono},
            Env__ = set_meta(Env_, Id, TM),
            {Env__, TM};
        false -> 
            terr("unifyTMeta failed: " ++ showType(M) ++ ":=" ++ showType(T))
end.

subsume(Env, Tvs, A, {tForall, _, _}=B) ->
    Sk = freshTSkol(),
    {tSkol, SkId} = Sk,
    unify(Env, [SkId] ++ Tvs, A, openTForall(B, Sk));
subsume(Env, Tvs, {tForall, _, _}=A, B) ->
    {Env_, M} = freshTMeta(Env, Tvs),
    unify(Env_, Tvs, openTForall(A, M), B);
subsume(Env, Tvs, A, B) -> unify(Env, Tvs, A, B).

% Inference/ Synthesis
synth(Env, _Tvs, {var, Name}) ->
    case get_binding(Env, Name) of 
        not_found -> terr("undefined var : " ++  Name);
        Ty -> {Env, Ty}
    end;
synth(Env, Tvs, {ann, Term, Type}) ->
    check(Env, Tvs, Term, Type);
synth(Env, Tvs, {app, _Left, _Right}=Term) ->
    {FT, As} = flattenApp(Term),
    {Env_, Ty} = synth(Env, Tvs, FT),
    synthapps(Env_, Tvs, Ty, As, null, []);
synth(Env, Tvs, {abs, Name, Body}) ->
    {Env_1, A} = freshTMeta(Env, Tvs, true),
    {Env_2, B} = freshTMeta(Env_1, Tvs),
    {Env_3, _} = check(set_binding(Env_2, Name, A), Tvs, Body, B),
    {Env_3, tFun(A, B)};
synth(_, _, Term) ->
    terr("cannot synth : " ++ showTerm(Term)).

synthapps(Env, Tvs, {tForall, _, _} = Ty, As, Ety, Acc) ->
    {Env_, M}= freshTMeta(Env, Tvs),
    synthapps(Env_, Tvs, openTForall(Ty, M), As, Ety, Acc);
synthapps(Env, Tvs, {tFun, Left, Right}, As, Ety, Acc) when length(As) > 0 ->
    [TM | AsTail] = As,
    Acc_ = Acc ++ [{TM, Left}],
    synthapps(Env, Tvs, Right, AsTail, Ety, Acc_);
synthapps(Env, Tvs, {tMeta, Id_m, _, _, _}, As, Ety, Acc) when length(As) > 0 ->
    {tMeta, Id_m, Tvs_m, Type, Mono} = get_meta(Env, Id_m),
    case Type of
        null  -> 
            {Env_A, A}  = freshTMeta(Env, Tvs_m),
            {Env_B, B} = freshTMeta(Env_A, Tvs_m),
            % ty.type = TFun(a, b),
            %  BUG: Potential
            Ty_Type = tFun(A, B),
            Env_ = set_meta(Env_B, Id_m, {tMeta, Id_m, Tvs_m, Ty_Type, Mono}),
            [TM | AsTail] = As,
            Acc_ = Acc ++ [{TM, A}],
            synthapps(Env_, Tvs, B, AsTail, Ety, Acc_);
        Valid -> synthapps(Env, Tvs, Valid, As, Ety, Acc)
    end;
synthapps(_, _, Ty, As, _, _) when length(As) > 0 ->
    terr("synthapps failed, not a function type: " ++ showType(Ty));
synthapps(Env, Tvs, Ty, _As, Ety, Acc) ->
    Env__ = case Ety of
        null    -> pickAndCheckArgs(Env, Tvs, Acc);
        NotNull ->
            {Env_, _T} = unify(Env, Tvs, Ty, NotNull),
            pickAndCheckArgs(Env_, Tvs, Acc)
    end,
    {Env__, Ty}.

% Bug to check
pickAndCheckArgs(Env, _, []) -> Env;
pickAndCheckArgs(Env, Tvs, Acc) ->
    {Env_1, {{Tm, TmTy}, RestAcc}} = pickArg(Env, Acc),
    {Env_2, _T} = check(Env_1, Tvs, Tm, TmTy),
    pickAndCheckArgs(Env_2, Tvs, RestAcc).

% Bug to check
pickArg(Env, Acc) ->
    pickArg_(Env, [], Acc).
pickArg_(Env, [Acc_HD | Acc_Rem], []) ->
    % Nothing match return shift
    Res = {Acc_HD, Acc_Rem},
    {Env, Res};
pickArg_(Env, Acc_Done, [{F,S} | Acc_Rem]) ->
    {Env_, PTS} = prune(Env, S),
    case PTS of
        {tMeta, _, _, _, _} ->
            pickArg_(Env_, Acc_Done ++ [{F,S}], Acc_Rem);
        _ ->
            {Env_, {{F,S}, Acc_Done ++ Acc_Rem}}
    end.

check(Env, Tvs, Term, {tMeta, Id_m, _, _, _} = Ty) ->
    {tMeta, Id_m, _, Type, _} = get_meta(Env, Id_m),
    case Type of
        null -> synthAndSubsume(Env, Tvs, Term, Ty);
        ValidType -> check(Env, Tvs, Term, ValidType)
    end;
    
check(Env, Tvs, Term, {tForall, _, _} = Ty) ->
    Sk = freshTSkol(),
    {tSkol, SkId} = Sk,
    check(Env, [SkId] ++ Tvs, Term, openTForall(Ty, Sk));
check(Env, Tvs, {abs, Name, Body}, {tFun, Left, Right}) ->
    check(set_binding(Env, Name, Left), Tvs, Body, Right);
check(Env, Tvs, {app, _, _} = Term, Ty) ->
    {FT, As} = flattenApp(Term),
    {Env_, FTy} = synth(Env, Tvs, FT),
    synthapps(Env_, Tvs, FTy, As, Ty, []);
check(Env, Tvs, Term, Ty) -> synthAndSubsume(Env, Tvs, Term, Ty).

synthAndSubsume(Env, Tvs, Term, Ty) ->
    {Env_, Inf} = synth(Env, Tvs, Term),
    subsume(Env_, Tvs, Inf, Ty).

infer(Env, Term) ->
    {Env_, Ty} = synth(Env, [], Term),
    Ty_ = applyEnv(Env_, Ty),
    % ?PRINT(Ty_),
    % ?PRINT(Env_#ten.metaMap),
    {_, PTy} = prune(Env_, Ty_),
    PTy.

%% ------------- Tests ------------%%
% Helpers for testing
v(N) -> var(N).
tv(N) -> tVar(N).
tid() -> tForall("t", tFun(tv("t"), tv("t"))).
listT(T) -> tApp(tv("List"), T).
st(S, T) -> tApp(tApp(tv("ST"), S), T).
pair(A, B) -> tApp(tApp(tv("Pair"), A), B).

init_bindings() -> #{
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

init_env() -> #ten
{
    bindings = init_bindings(),
    metaMap = #{}
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

infer_term(Term) -> 
    try
        Ty = infer(init_env(), Term), 
        Res = showTerm(Term) ++ " :: " ++ showType(Ty),
        io:fwrite("~p ~n", [Res]) 
    catch
        error: Reason -> 
        MSG = showTerm(Term) ++ " :: " ++ Reason,
        io:fwrite("~p ~n",[MSG])
    end.

all_tests() ->
    lists:map(fun(Term) -> infer_term(Term) end, test_cases()),
    done.

tests_full_infer() ->
    % Term = app(app(v("choose"), v("Nil")), v("ids")),
    Term = app(app(v("k"), v("h")), v("l")), % X
    % Term = app(v("f"), app(v("choose"), v("id"))) ,% X
    % Term = app(v("choose"), v("id")) ,% X
    % Term = app(v("choose"), v("Nil")), 
    % Term = v("ids"),
    Ty = infer(init_env(), Term),
    % ?PRINT(Ty),
    Res = showTerm(Term) ++ " :: " ++ showType(Ty),
    io:fwrite("Type Res: ~p ~n",[Res]).