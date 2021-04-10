-module(btc).

-import(erl_syntax,[
    function_clauses/1,
    fun_expr_clauses/1,
    clause_patterns/1,
    clause_body/1,
    clause_guard/1,
    type/1
]).

-export([tests_full_infer/0, all_tests/0]).
-export([type_check/2]).

%% PRINT Debugging macro%%
-ifndef(PRINT).
-define(PRINT(Var), io:format("DEBUG: ~p:~p - ~p~n~n ~p~n~n", [?MODULE, ?LINE, ??Var, Var])).
-endif.

%% BDTC - Start %%

% Helpers for testing
v(N) -> var(N).
tv(N) -> hm:tvar(N, 0).
tid() -> hm:forall("t", [], hm:funt([tv("t")], tv("t"), 0), 0).
listT(T) -> hm:tcon("List", [T], 0).
st(S, T) -> hm:tcon(hm:tcon("ST", [S], 0), [T], 0).
pair(A, B) -> hm:tcon(hm:tcon("Pair", [A], 0), [B], 0).

init_bindings() -> #{
"head" => hm:forall("t", [], hm:funt([listT(tv("t"))], tv("t"), 0), 0),
"tail" => hm:forall("t", [], hm:funt([listT(tv("t"))], listT(tv("t")), 0), 0),
"Nil" => hm:forall("t", [], listT(tv("t")), 0),
"Cons" => hm:forall("t", [], hm:funt([tv("t")], hm:funt([listT(tv("t"))], listT(tv("t")), 0), 0), 0),
"single" => hm:forall("t", [], hm:funt([tv("t")], listT(tv("t")), 0), 0),
"append" => hm:forall("t", [], hm:funt([listT(tv("t"))], hm:funt([listT(tv("t"))], listT(tv("t")), 0), 0), 0),
"length" => hm:forall("t", [], hm:funt([listT(tv("t"))], tInt(), 0), 0),
"runST" => hm:forall("t", [], hm:funt([hm:forall("s", [], st(tv("s"), tv("t")), 0)], tv("t"), 0), 0),
"argST" => hm:forall("s", [], st(tv("s"), tInt()), 0),
"pair" => hm:forall("a", [], hm:forall("b", [], hm:funt([tv("a")], hm:funt([tv("b")], pair(tv("a"), tv("b")), 0), 0), 0), 0),
"pair2" => hm:forall("b", [], hm:forall("a", [], hm:funt([tv("a")], hm:funt([tv("b")], pair(tv("a"), tv("b")), 0), 0), 0), 0),
"id" => tid(),
"ids" => listT(tid()),
"inc" => hm:funt([tInt()], tInt(), 0),
"choose" => hm:forall("t", [], hm:funt([tv("t")], hm:funt([tv("t")], tv("t"), 0), 0), 0),
"poly" => hm:funt([tid()], pair(tInt(), tBool()), 0),
"auto" => hm:funt([tid()], tid(), 0),
"auto2" => hm:forall("b", [], hm:funt([tid()], hm:funt([tv("b")], tv("b"), 0), 0), 0),
"map" => hm:forall("a", [], hm:forall("b", [], hm:funt([hm:funt([tv("a")], tv("b"), 0)], hm:funt([listT(tv("a"))], listT(tv("b")), 0), 0), 0), 0),
"app" => hm:forall("a", [], hm:forall("b", [], hm:funt([hm:funt([tv("a")], tv("b"), 0)], hm:funt([tv("a")], tv("b"), 0), 0), 0), 0),
"revapp" => hm:forall("a", [], hm:forall("b", [], hm:funt([tv("a")], hm:funt([hm:funt([tv("a")], tv("b"), 0)], tv("b"), 0), 0), 0) , 0),
"f" => hm:forall("t", [], hm:funt([hm:funt([tv("t")], tv("t"), 0)], hm:funt([listT(tv("t"))], tv("t"), 0), 0), 0),
"g" => hm:forall("t", [], hm:funt([listT(tv("t"))], hm:funt([listT(tv("t"))], tv("t"), 0), 0), 0),
"k" => hm:forall("t", [], hm:funt([tv("t")], hm:funt([listT(tv("t"))], tv("t"), 0), 0), 0),
"h" => hm:funt([tInt()], tid(), 0),
"l" => listT(hm:forall("t", [], hm:funt([tInt()], hm:funt([tv("t")], tv("t"), 0), 0), 0)),
"r" => hm:funt([hm:forall("a", [], hm:funt([tv("a")], tid(), 0), 0)], tInt(), 0)
}.

% Built In Types
tBool() -> hm:bt(bool, 0).
tInt() -> hm:bt(integer, 0).

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
    Res = hm:pretty(Ty). %,
    % " ".
    % ?PRINT(Ty),
    % {TyStr, _} = showType_(Ty, init_meta()),
    % TyStr.

showType_({tVar, Name}, State) -> {Name, State};
showType_({bt, Name}, State) -> {atom_to_list(Name), State};
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
showType_({funt, Left, Right}, State) ->
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

%% prune can modify the state of tMeta type.
%% So passing Env to track.
prune(Env, {tMeta, _, Id_m, _, _, _}) ->
    {tMeta, _, Id_m, Tvs, Type, Mono} = env:get_meta(Env, Id_m),
    case Type of 
        null -> {Env, {tMeta, 0, Id_m, Tvs, Type, Mono}};
        Valid ->
            {Env_1, PT} = prune(Env, Valid),
            UpdatedMeta = {tMeta, 0, Id_m, Tvs, PT, Mono},
            Env_2 = env:set_meta(Env_1, Id_m, UpdatedMeta),
            {Env_2, PT}
            % {Env_2, UpdatedMeta}
    end;
prune(Env, {funt, _, [ArgT], RetT}) ->
    {Env_L, PT_L} = prune(Env, ArgT),
    {Env_R, PT_R} = prune(Env_L, RetT),
    {Env_R, hm:funt([PT_L], PT_R, 0)};
prune(Env, {tcon, _,Left, [Right]}) ->
    {Env_L, PT_L} = prune(Env, Left),
    {Env_R, PT_R} = prune(Env_L, Right),
    {Env_R, hm:tcon(PT_L, [PT_R], 0)};
prune(Env, {forall, Name, _, Body}) ->
    {Env_, PT} = prune(Env, Body),
    {Env_, {forall, Name, [], PT}};
prune(Env, T) -> {Env, T}.

applyEnv(Env, {tMeta, _, Id, _, _, _}) ->
    Res = env:get_meta(Env, Id),
    Res;
applyEnv(Env, {funt, _, As, Right}) ->
    As_ = lists:map(fun(A) -> applyEnv(Env, A) end, As),
    hm:funt(As_, applyEnv(Env, Right), 0);
applyEnv(Env, {tcon, _, Left, [Right]}) -> 
    hm:tcon(applyEnv(Env, Left), [applyEnv(Env, Right)], 0);
applyEnv(Env, {forall, Name, _, Body}) -> 
    {forall, Name, [], applyEnv(Env, Body)};
applyEnv(_, T) -> T.
% applyEnv(_, T) -> ?PRINT(T), T.

flattenApp({app, Left, Right}) ->
    {T, Args} = flattenApp (Left),
    {T, Args ++ [Right]};
    % {T, [Right] ++ Args};
flattenApp(T) -> {T, []}.

% when Name == X
substTVar(X, S, {tvar, _, _Name} = TVar) when TVar == X -> S;
substTVar(X, S, {tMeta, _ , _Id, _Tvs, Type, _}) when Type /= null ->
    substTVar(X, S, Type);
substTVar(X, S, {funt, _, [Left], Right}) ->
    hm:funt([substTVar(X, S, Left)], substTVar(X, S, Right), 0);
substTVar(X, S, {tcon, _, Left, [Right]}) ->
    hm:tcon(substTVar(X, S, Left), [substTVar(X, S, Right)], 0);
substTVar(X, S, {forall, Name, _, Body}) when Name /= X ->
    {forall, Name, [], substTVar(X, S, Body)};
substTVar(_X, _S, T) -> T.

openTForall({forall, Name, _, Body}, T) -> substTVar(Name, T, Body).

% Subtyping
checkSolution(Env, T, T) -> {Env, false};
checkSolution(Env, {tMeta, _, Id_m, _, _, _} = M, {tMeta, _, Id_t, _, _, _}) ->
% todo     if (m.mono) t.mono = true;
    {tMeta, _, Id_m, Tvs_m, _, Mono_m} = env:get_meta(Env, Id_m),
    {tMeta, _, Id_t, Tvs_t, Type_t, _} = env:get_meta(Env, Id_t),
    Env_ = case Mono_m of
        true -> env:set_meta(Env, Id_t, {tMeta, 0, Id_t, Tvs_t, Type_t, true});
        false -> Env
    end,
    case Type_t of
        null -> checkSolution(Env_, M, Type_t);
        _    -> {Env_, subset(Tvs_m, Tvs_t)}
    end;
checkSolution(Env, M, {funt, _, [Left], Right}) ->
    {Env_, LRes} = checkSolution(Env, M, Left),
    {Env__, RRes} = checkSolution(Env_, M, Right),
    {Env__, LRes and RRes};
checkSolution(Env, M, {tcon, _, Left, [Right]}) ->
    {Env_, LRes} = checkSolution(Env, M, Left),
    {Env__, RRes} = checkSolution(Env_, M, Right),
    {Env__, LRes and RRes};
checkSolution(Env, {tMeta, _, Id_m, _, _, _} = M, {forall, _, _, Body}) ->
    {tMeta, _, Id_m, _, _, Mono} = env:get_meta(Env, Id_m),
    case Mono of
        true -> {Env, false};
        false -> checkSolution(Env, M, Body)
    end;
checkSolution(Env, {tMeta, _, Id_m, _, _, _}, {tSkol,_, Id}) ->
    {tMeta, _, Id_m, Tvs, _, _} = env:get_meta(Env, Id_m),
    {Env, lists:member(Id, Tvs)};
checkSolution(Env, _M, _T) -> {Env, true}.

%% Clean up unify to use tvar functions
unify(Env, _Tvs, A, A) -> {Env, A};
unify(Env, _Tvs, {tvar, _, Name_A}, {tvar, _, Name_B}) when Name_A == Name_B ->
    {Env, hm:tvar(Name_A, 0)};
unify(Env, Tvs, {funt, _, [Left_A], Right_A}, {funt, _, [Left_B], Right_B}) ->
    {Env_, Left_U} = unify(Env, Tvs, Left_A, Left_B),
    {Env__, Right_U} = unify(Env_, Tvs, Right_A, Right_B),
    {Env__, hm:funt([Left_U], Right_U, 0)};
unify(Env, Tvs, {tcon, _, Left_A, [Right_A]}, {tcon, _, Left_B, [Right_B]}) ->
    {Env_, Left_U} = unify(Env, Tvs, Left_A, Left_B),
    {Env__, Right_U} = unify(Env_, Tvs, Right_A, Right_B),
    {Env__, hm:tcon(Left_U, [Right_U], 0)};
unify(Env, Tvs, {forall, Name_A, _, Body_A}=A, {forall, Name_A, _, Body_A}=B) ->
    Sk = hm:freshTSkol(),
    {tSkol, _, SkId} = Sk,
    unify(Env, [SkId] ++ Tvs, openTForall(A, Sk), openTForall(B, Sk));
unify(Env, Tvs, {tMeta, _, Id_m, _, _, _}, B) ->
    A = env:get_meta(Env, Id_m),
    unifyTMeta(Env, Tvs, A, B);
unify(Env, Tvs, A , {tMeta, _, Id_m, _, _, _}) ->
    B = env:get_meta(Env, Id_m),
    unifyTMeta(Env, Tvs, B, A);
unify(_Env, _Tvs, A, B) ->
    io:fwrite("unify failed with types ",[]),
    showType(A),
    io:fwrite(" :=: ",[]),
    showType(B),
    io:fwrite("~n",[]),
    terr("unify failed!").

unifyTMeta(Env, _Tvs, M, M) -> {Env, M};
unifyTMeta(Env, Tvs, {tMeta, _, _, _, Type, _}, T) when Type /= null ->
    unify(Env, Tvs, Type, T);
unifyTMeta(Env, Tvs, M, {tMeta, _, _, _, Type, _}) when Type /= null ->
    unifyTMeta(Env, Tvs, M, Type);
unifyTMeta(Env, Tvs, {tMeta, _, Id, _, _, Mono}=M, T) ->
    {Env_, Res} = checkSolution(Env, M, T),
    case Res of
        true  ->
            TM = {tMeta, 0, Id, Tvs, T, Mono},
            Env__ = env:set_meta(Env_, Id, TM),
            {Env__, TM};
        false -> 
            terr("unifyTMeta failed: " ++ showType(M) ++ ":=" ++ showType(T))
end.

subsume(Env, Tvs, Inf, {forall,_, _, _}=Ty) ->
    Sk = hm:freshTSkol(),
    {tSkol, _, SkId} = Sk,
    unify(Env, [SkId] ++ Tvs, Inf, openTForall(Ty, Sk));
subsume(Env, Tvs, {forall, _, _, _}=Inf, Ty) ->
    {Env_, M} = hm:freshTMeta(Env, Tvs, 0),
    unify(Env_, Tvs, openTForall(Inf, M), Ty);
subsume(Env, Tvs, Inf, Ty) ->
    unify(Env, Tvs, Inf, Ty).

% Inference/ Synthesis
synth(Env, _Tvs, {const, bool}) ->
    {Env, tBool()};
synth(Env, _Tvs, {var, Name}) ->
    case env:lookup(Name, Env) of
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
    {Env_1, A} = hm:freshTMeta(Env, Tvs, true, 0),
    {Env_2, B} = hm:freshTMeta(Env_1, Tvs, 0),
    {Env_3, _} = check(env:extend(Name, A, Env_2), Tvs, Body, B),
    {Env_3, hm:funt([A], B, 0)};
synth(Env, Tvs, {func, FName, VName, Body}) ->
    {Env_1, A} = hm:freshTMeta(Env, Tvs, true, 0),
    {Env_2, B} = hm:freshTMeta(Env_1, Tvs, 0),
    FT = hm:funt([A], B, 0),
    Env_3 = env:extend(FName, FT, Env_2),
    {Env_4, _} = check(env:extend(VName, A, Env_3), Tvs, Body, B),
    {Env_4, hm:funt([A], B, 0)};
synth(Env, Tvs, {if_else, Cond, TB, FB}) ->
    {Env_1, A} = hm:freshTMeta(Env, Tvs, 0),
    {Env_2, _} = check(Env_1, Tvs, Cond, tBool()),
    {Env_3, _} = check(Env_2, Tvs, TB, A),
    {Env_4, _} = check(Env_3, Tvs, FB, A),
    {Env_4, A};
synth(_, _, Term) ->
    terr("cannot synth : " ++ showAny(Term)).

synthapps(Env, Tvs, {forall, _, _, _} = Ty, As, ExpectedType, Acc) ->
    {Env_, M}= hm:freshTMeta(Env, Tvs, 0),
    synthapps(Env_, Tvs, openTForall(Ty, M), As, ExpectedType, Acc);
synthapps(Env, Tvs, {funt, _, [Left], Right}, As, ExpectedType, Acc) when length(As) > 0 ->
    [TM | AsTail] = As,
    Acc_ = Acc ++ [{TM, Left}],
    synthapps(Env, Tvs, Right, AsTail, ExpectedType, Acc_);
synthapps(Env, Tvs, {tMeta, _, Id_m, _, _, _}, As, ExpectedType, Acc) when length(As) > 0 ->
    {tMeta, _, Id_m, Tvs_m, Type, Mono} = env:get_meta(Env, Id_m),
    case Type of
        null  -> 
            {Env_A, A}  = hm:freshTMeta(Env, Tvs_m, 0),
            {Env_B, B} = hm:freshTMeta(Env_A, Tvs_m, 0),
            % ty.type = TFun(a, b),
            %  BUG: Potential
            Ty_Type = hm:funt([A], B,0),
            Env_ = env:set_meta(Env_B, Id_m, {tMeta, 0, Id_m, Tvs_m, Ty_Type, Mono}),
            [TM | AsTail] = As,
            Acc_ = Acc ++ [{TM, A}],
            synthapps(Env_, Tvs, B, AsTail, ExpectedType, Acc_);
        Valid -> synthapps(Env, Tvs, Valid, As, ExpectedType, Acc)
    end;
synthapps(_, _, SynthFailTy, As, _, _) when length(As) > 0 ->
    terr("synthapps failed, not a function type: " ++ showType(SynthFailTy));
synthapps(Env, Tvs, Ty, _As, ExpectedType, Acc) ->
    Env__ = case ExpectedType of
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
        {tMeta, _, _, _, _, _} ->
            pickArg_(Env_, Acc_Done ++ [{F,S}], Acc_Rem);
        _ ->
            {Env_, {{F,S}, Acc_Done ++ Acc_Rem}}
    end.

check(Env, Tvs, Term, {tMeta, _, Id_m, _, _, _} = Ty) ->
    {tMeta, _, Id_m, _, Type, _} = env:get_meta(Env, Id_m),
    case Type of
        null -> synthAndSubsume(Env, Tvs, Term, Ty);
        ValidType -> check(Env, Tvs, Term, ValidType)
    end;
    
check(Env, Tvs, Term, {forall, _, _, _} = Ty) ->
    Sk = hm:freshTSkol(0),
    {tSkol, _, SkId} = Sk,
    check(Env, [SkId] ++ Tvs, Term, openTForall(Ty, Sk));
check(Env, Tvs, {abs, Name, Body}, {funt, _, [Left], Right}) ->
    check(env:extend(Name, Left, Env), Tvs, Body, Right);
check(Env, Tvs, {app, _, _} = Term, Ty) ->
    {FT, As} = flattenApp(Term),
    {Env_, FTy} = synth(Env, Tvs, FT),
    synthapps(Env_, Tvs, FTy, As, Ty, []);
check(Env, Tvs, {if_else, Cond, TB, FB}, Ty) ->
    {Env_1, _} = check(Env, Tvs, Cond, tBool()),
    {Env_2, _} = check(Env_1, Tvs, TB, Ty),
    {Env_3, _} = check(Env_2, Tvs, FB, Ty),
    {Env_3, Ty};
check(Env, Tvs, Term, Ty) ->
    synthAndSubsume(Env, Tvs, Term, Ty).

synthAndSubsume(Env, Tvs, Term, Ty) ->
    {Env_, Inf} = btc_synth(Env, Tvs, Term),
    subsume(Env_, Tvs, Inf, Ty).

infer(Env, Term) ->
    {Env_, Ty} = synth(Env, [], Term),
    % ?PRINT(Ty),
    Ty_ = applyEnv(Env_, Ty),
    % ?PRINT(Ty_),
    % ?PRINT(env:get_meta_map(Env_)),
    {_, PTy} = prune(Env_, Ty_),
    PTy.

init_btc_env()->
    maps:fold(
        fun(X, T, Env) -> env:extend(X, T, Env) end,
        env:empty(),
        init_bindings()).

tests_full_infer() ->
    % Term = app(app(v("choose"), v("Nil")), v("ids")),
    Term = app(app(v("revapp"), v("argST")), v("runST")),
    % Term = abs("x", c_bool()),
    % Term = func("foo", "x", app(v("foo"), v("x"))),
    % Term = if_else(c_bool(), c_bool(), c_bool()),
    % Term = ann(if_else(c_bool(), c_bool(), v("id")), tBool()),
    % Term = ann(c_bool(), tBool()),
    % Term = app(v("f"), app(v("choose"), v("id"))) ,% X
    % Term = app(v("choose"), v("id")) ,% X
    % Term = app(app(v("choose"), v("id")), v("auto2")),
    % Term = app(app(v("k"), v("h")), v("l")), %% X
    % Term = app(v("choose"), v("Nil")),
    % Term = v("choose"),
    % Term = v("Nil"),
    % Term = v("id"),
    % Term = v("ids"),
    % Term = v("k"),
    % Term = v("h"),
    % Term = v("l"),
    Ty = infer(init_btc_env(), Term),
    ?PRINT(Ty),
    io:fwrite("Type Res: ",[]),
    showTerm(Term),
    io:fwrite(" :: ",[]),
    showType(Ty),
    io:fwrite("~n",[]),
    okie.

% Terms
var(Name)        -> {var, Name}.
c_bool()         -> {const, bool}.
abs(Name, Body)  -> {abs, Name, Body}.
app(Left, Right) -> {app, Left, Right}.
ann(Term, Type)  -> {ann, Term, Type}.
func(FName, VName, Body) -> {func, FName, VName, Body}.
if_else(Cond, TB, FB) -> {if_else, Cond, TB, FB}.

showTerm({var, Name}) ->  io:fwrite("~s",[Name]) ;
showTerm({abs, Name, Body}) ->
    io:fwrite("(\\~s.",[Name]),
    showTerm(Body),
    io:fwrite(")");
showTerm({func, FName, _VName, _Body}) ->
    io:fwrite("(fun: ~p)", [FName]);
showTerm({app, Left, Right}) ->
    io:fwrite("(", []),
    showTerm(Left),
    io:fwrite(" ",[]),
    showTerm(Right),
    io:fwrite(")",[]);
showTerm({ann, Term, Type}) ->
    io:fwrite("(", []),
    showTerm(Term),
    io:fwrite(" : ",[]),
    showType(Type),
    io:fwrite(")",[]);
showTerm({const, bool}) ->
    "C(Bool)";
showTerm({if_else, Cond, TB, FB}) ->
    io:fwrite("(", []),
    showTerm(Cond),
    io:fwrite("?", []),
    showTerm(TB),
    io:fwrite(":", []),
    showTerm(FB),
    io:fwrite(")", []);
showTerm(Term) -> "Cannot show Unknown term: " ++ showAny(Term).

test_cases() -> [
  % A
  abs("x", abs("y", v("x"))),
  app(v("choose"), v("id")),
  ann(app(v("choose"), v("id")), hm:funt([tid()], tid(), 0)),
  app(app(v("choose"), v("Nil")), v("ids")),
  app(v("id"), v("auto")),
  app(v("id"), v("auto2")),  
  app(app(v("choose"), v("id")), v("auto")),
  app(app(v("choose"), v("id")), v("auto2")), % X
  app(app(v("f"), app(v("choose"), v("id"))), v("ids")), % X
  app(app(v("f"), ann(app(v("choose"), v("id")), hm:funt([tid()], tid(), 0))), v("ids")),
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

infer_term(Term) -> 
    try
        showTerm(Term),
        io:fwrite(" :: "),
        Ty = infer(init_btc_env(), Term),
        showType(Ty),
        io:fwrite("~n",[])
    catch
        error: Reason ->
        % showTerm(Term),
        % io:fwrite("~n",[]),
        type_error
    end.

all_tests() ->
    lists:map(fun(Term) -> infer_term(Term) end, test_cases()),
    done.
%% BDTC - End %%

type_check(Env, F) ->
    FunQName = util:getFnQName(F),
    Specs = env:getSpecs(Env),
    case spec:hasUserSpecifiedSpec(Specs, FunQName) of
        true ->
            SpecFT = spec:getFirstSpecType(Specs, FunQName),
            do_btc_check(Env, F, SpecFT);
        false -> do_btc_infer(Env, F)
    end.

do_btc_check(Env, F, SpecFT) ->
    FunQName = util:getFnQName(F),
    {Env, Result, Type} = btc_check(Env, [], F, SpecFT),
    case Result of
        false -> erlang:error({type_error
                               , "Check failed for the function:: " ++ util:to_string(FunQName)});
        true  -> true
    end.

do_btc_infer(Env, F) ->
    FunQName = util:getFnQName(F),
    ?PRINT(FunQName),
    {SEnv, STy} = btc_synth(Env, [], F),
    Ty_ = applyEnv(SEnv, STy),
    % ?PRINT(Ty_),
    % ?PRINT(env:get_meta_map(Env_)),
    {_, PTy} = prune(SEnv, Ty_),
    ?PRINT(PTy),
    showType(PTy),
    io:fwrite("~n",[]),
    Env.

-spec btc_check(hm:env(), [any()], erl_syntax:syntaxTree(), hm:type()) ->
    {hm:env(),  hm:type()}.
btc_check(Env, Tvs, {integer,L,_}, Type) ->
    Inferred = hm:bt(integer, L),
    case hm:is_type_var(Type) of
        true  ->
            Env1 = env:extend_type_var(Type, Inferred, Env),
            {Env1, Inferred};
        false ->
            IsSame = hm:isSubType(Inferred, Type),
            {Env, Inferred}
    end;
btc_check(Env, Tvs, {string, L,_}, Type) ->
    Inferred = hm:tcon("List", [hm:bt(char,L)],L),
    IsSame = hm:isSubType(Inferred, Type),
    {Env, Inferred};
btc_check(Env, Tvs, {char, L,_}, Type) ->
    Inferred = hm:bt(char,L),
    IsSame = hm:isSubType(Inferred, Type),
    {Env, Inferred};
btc_check(Env, Tvs, {float,L,_}, Type) ->
    Inferred = hm:bt(float, L),
    IsSame = hm:isSubType(Inferred, Type),
    {Env, Inferred};
btc_check(Env, Tvs, {atom,L,X}, Type) ->
    Inferred = case X of
        B when is_boolean(B) -> hm:bt(boolean, L);
        _                    -> hm:bt(atom, L)
        end,
    IsSame = hm:isSubType(Inferred, Type),
    {Env, Inferred};
btc_check(Env, Tvs, {var, L, '_'}, Type) ->
    {Env, Type};
btc_check(Env, Tvs, {var, L, X}, Type) ->
    case env:is_bound(X,Env) of
        true  ->
            VarT = lookup(X, Env, L),
            % ?PRINT(VarT),
            synthAndSubsume(Env, Tvs, {var, L, X}, Type);
            % check_type_var(Env, Type, VarT);
        false -> 
            VarT = hm:replaceLn(Type, L),
            Env_ = env:extend(X, VarT, Env),
            % check_type_var(Env, Type, VarT),
            {Env_, VarT}
    end;
btc_check(Env, Tvs, {match, L, _LNode, _RNode} = Node, Type) ->
    ?PRINT(Node),
    {ResType, InfCs, InfPs} = etc:infer(Env, Node),
    % Solve unification constraints
    Sub = hm:solve(InfCs),
    Ps = hm:subPs(InfPs,Sub),
    % predicate solving leads in a substitution since 
    % oc predicates are basically ambiguous unification constraints
    {Sub_, RemPs} = hm:solvePreds(rt:defaultClasses(), Ps),
    SubdEnv = hm:subE(Env, hm:comp(Sub_, Sub)),
    {VarT, _Ps} = etc:lookup('X', SubdEnv, L),
    ?PRINT(VarT),
    {SubdEnv, Type};
btc_check(Env, Tvs, {op, L, Op, E1, E2}, Type) ->
    OpType = lookup(Op, Env, L),
    case hm:has_type_var(OpType) of
        true  ->
            StrippedType = hm:type_without_bound(OpType),
            Arg1Type = hd(hm:get_fn_args(StrippedType)),
            Arg2Type = lists:last(hm:get_fn_args(StrippedType)),
            {Env1, Res1, _T1} = btc_check(Env, Tvs, E1, Arg1Type),
            {Env2, Res2, _T2} = btc_check(Env1, Tvs, E2, Arg2Type),
            Env_Solved = env_solver:solve_envs(Env1, Env2),
            {Env_Solved, Type};
        false ->
            Arg1Type = hd(hm:get_fn_args(OpType)),
            Arg2Type = lists:last(hm:get_fn_args(OpType)),
            RetType = hm:get_fn_rt(OpType),
            {Env1, Res1, _T1} = btc_check(Env, Tvs, E1, Arg1Type),
            {Env2, Res2, _T2} = btc_check(Env1, Tvs, E2, Arg2Type),
            IsSame = hm:isSubType(RetType, Type),
            {Env2,  RetType}
    end;

btc_check(Env, Tvs, {clause, L, _, _, _}=Clause, Type) ->
    % ClausePatterns = clause_patterns(Clause),
    ClauseBody = clause_body(Clause),
    % {EnvPat, PatResults, _} = checkPatterns(Env, ClausePatterns, Type),
    % PatRes = lists:foldl(
    %     fun(ARes, Res) ->
    %         ARes and Res
    %     end, true, PatResults),
    % ClauseGuards = clause_guard(Node),
    BodyType = hm:get_fn_rt(Type),
    {Env_, BodyRes, _} = checkClauseBody(Env, Tvs, ClauseBody, BodyType),
    {Env_, Type};
btc_check(Env, Tvs, Node, Type) ->
    case type(Node) of
        Fun when Fun =:= function; Fun =:= fun_expr ->
            Clauses = case Fun of
                function -> function_clauses(Node);
                fun_expr -> fun_expr_clauses(Node)
            end,
            ClausesCheckRes = lists:map(fun(C) -> btc_check(Env, Tvs, C, Type) end, Clauses),
            Result = lists:foldl(
                fun({_Env, Res, _T}, AccRes) ->
                    AccRes and Res
                end, true, ClausesCheckRes),
            {Env, Type};
        _ -> synthAndSubsume(Env, Tvs, Node, Type)
    end;
btc_check(Env, Tvs, Term, Ty) ->
    synthAndSubsume(Env, Tvs, Term, Ty).


-spec btc_synth(hm:env(), [any()], erl_syntax:syntaxTree()) ->
    {hm:env(), hm:type()}.
btc_synth(Env, _Tvs, {integer, L, _}) ->
    Inferred = hm:bt(integer, L),
    {Env, Inferred};
btc_synth(Env, _Tvs, {string, L,_}) ->
    Inferred = hm:tcon("List", [hm:bt(char,L)],L),
    {Env, Inferred};
btc_synth(Env, _Tvs, {char, L,_}) ->
    Inferred = hm:bt(char,L),
    {Env, Inferred};
btc_synth(Env, _Tvs, {float,L,_}) ->
    Inferred = hm:bt(float, L),
    {Env, Inferred};
btc_synth(Env, _Tvs, {atom,L,X}) ->
    Inferred = case X of
        B when is_boolean(B) -> hm:bt(boolean, L);
        _                    -> hm:bt(atom, L)
        end,
    {Env, Inferred};
btc_synth(Env, Tvs, {var, L, X}) ->
    case env:is_bound(X,Env) of
        true    ->
            T = lookup(X, Env, L),
            {Env, T};
        false   ->
            {Env_, A} = hm:freshTMeta(Env, Tvs, true, 0),
            {env:extend(X, A, Env_), A}
    end;
btc_synth(Env, Tvs, {clause, L, _, _, _}=Clause) ->
    ClausePatterns = clause_patterns(Clause),
    ClauseBody = clause_body(Clause),
    {Env_1, A} = btc_synth(Env, Tvs, hd(ClausePatterns)),
    {Env_2, B} = hm:freshTMeta(Env_1, Tvs, 0),
    % Env_3 = env:extend(Name, A, Env_2),
    {Env_3, Type} = btc_check(Env_2, Tvs, lists:last(ClauseBody), B),
    {Env_3, hm:funt([A], B, 0)};
btc_synth(Env, Tvs, Node) ->
    case type(Node) of
        Fun when Fun =:= function; Fun =:= fun_expr ->
            Clauses = case Fun of
                function -> function_clauses(Node);
                fun_expr -> fun_expr_clauses(Node)
            end,
            % ClausesCheckRes = lists:map(fun(C) -> btc_synth(Env, Tvs, C) end, Clauses),
            {Env_ , T} = btc_synth(Env, Tvs, hd(Clauses)),
            ?PRINT(T),
            {Env_ , T};
        X -> erlang:error({type_error," Cannot synthesize the type of " 
            ++ util:to_string(Node) ++ " with node type "++ util:to_string(X)})
    end.

% % check if the arg patterns are matching.
% -spec checkPatterns(hm:env(),[erl_syntax:syntaxTree()], hm:types()) -> 
%     {hm:env(), [boolean()], [hm:types()]}.
% checkPatterns(Env, ClausePatterns, Type) ->
%     ArgTypes = hm:get_fn_args(Type),
%     ArgAndTypes = lists:zip(ClausePatterns, ArgTypes),
%     lists:foldl(
%         fun({ArgPattern, ArgType},{Ei, AccRs, AccTs}) ->
%             {Env_, Res, CType} = checkArgType(Ei, ArgPattern, ArgType),
%             {Env_, AccRs ++ [Res], AccTs ++ [CType]}
%         end, {Env, [],[]}, ArgAndTypes).

% % check if the arg expr has given arg type.
% -spec checkArgType(hm:env(), erl_syntax:syntaxTree(), hm:types()) -> 
%     {hm:env(), boolean(), hm:types()}.
% checkArgType(Env, ArgPattern, ArgType) ->
%     check(Env, ArgPattern, ArgType).

% check if the arg patters are matching.
% given a body of a clause, returns its type
-spec checkClauseBody(hm:env(), [any()], erl_syntax:syntaxTree(), hm:type()) -> 
    {hm:env(), boolean(), hm:type()}.
checkClauseBody(Env, Tvs, BodyExprs, Type) ->
    % TODO: We have to add support for let recursively here
    % {Env_, CsBody, PsBody} = lists:foldl(
    %     fun(Expr, {Ei,Csi,Psi}) -> 
    %         {Ei_,Csi_,Psi_} = etc:checkExpr(Ei, Expr),
    %         {Ei_, Csi ++ Csi_, Psi ++ Psi_}
    %     end, {Env,[],[]}, lists:droplast(BodyExprs)),
    % SolvedEnv = localConstraintSolver(Env_, CsBody, PsBody),
    btc_check(Env, Tvs, lists:last(BodyExprs), Type).

% check if the arg patters are matching.
% given a body of a clause, returns its type
-spec inferClauseBody(hm:env(), [any()], erl_syntax:syntaxTree()) -> 
    {hm:env(), hm:types()}.
inferClauseBody(Env, Tvs, BodyExprs) ->
    % TODO: We have to add support for let recursively here
    % {Env_, CsBody, PsBody} = lists:foldl(
    %     fun(Expr, {Ei,Csi,Psi}) -> 
    %         {Ei_,Csi_,Psi_} = etc:checkExpr(Ei, Expr),
    %         {Ei_, Csi ++ Csi_, Psi ++ Psi_}
    %     end, {Env,[],[]}, lists:droplast(BodyExprs)),
    % SolvedEnv = localConstraintSolver(Env_, CsBody, PsBody),
    btc_synth(Env, Tvs, lists:last(BodyExprs)).

% -spec localConstraintSolver(hm:env(), [hm:constraint()], [hm:predicate()]) ->
%     hm:env().
% localConstraintSolver(Env, InfCs, InfPs) -> 
%     Sub = hm:solve(InfCs),
%     Ps = hm:subPs(InfPs, Sub),
%     {Sub_, _RemPs}   = hm:solvePreds(rt:defaultClasses(), Ps),
%     hm:subE(Env, hm:comp(Sub_, Sub)).

%% Look up for function type and specialize
-spec lookup(hm:tvar(),hm:env(),integer()) -> hm:type().
lookup(X,Env,L) ->
    case env:isGuardExprEnabled(Env) of
        false -> lookup_(X,Env,L);
        true  -> 
            case env:checkGuard(X,Env) of
                undefined   ->
                    lookup_(X, Env, L);
                T           -> T
            end
    end.

-spec lookup_(hm:tvar(),hm:env(),integer()) -> hm:type().
lookup_(X,Env,L) ->
    case env:lookup(X,Env) of
        undefined ->
            case env:lookup_ext_binding(X,Env) of 
                undefined ->
                    erlang:error({type_error,util:to_string(X) ++ 
                        " not bound on line " ++ util:to_string(L)});
                ET        -> ET
            end;
        T         -> T
    end.

% lookupRemote(X,Env,L,Module) ->
%     case env:lookupRemote(Module, X, Env) of
%         undefined   ->
%                 erlang:error({type_error,util:to_string(X) ++ 
%                             " on line " ++ util:to_string(L) ++ 
%                             " is not exported by module " ++ util:to_string(Module)});
%         na          ->
%             {_,ArgLen} = X,
%             ArgTypes = lists:map(fun hm:fresh/1, lists:duplicate(ArgLen,L)),
%             {hm:funt(ArgTypes,hm:fresh(L),L),[]};
%         T           -> 
%             {FT,Ps} = hm:freshen(T), 
%             {hm:replaceLn(FT,0,L),Ps}
%     end.

check_type_var(Env, Type, Inferred)->
case hm:is_type_var(Type) of
    true  ->
        case env:lookup_type_var(Type, Env) of
            VarType ->
                IsSame = hm:isSubType(VarType, Inferred),
                {Env, IsSame, Inferred};
            undefined ->
                Env1 = env:extend_type_var(Type, Inferred, Env),
                {Env1, true, Inferred}
        end;
    false ->
        IsSame = hm:isSubType(Inferred, Type),
        {Env, IsSame, Inferred}
end.