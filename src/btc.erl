-module(btc).

-import(erl_syntax,[
    function_clauses/1,
    fun_expr_clauses/1,
    clause_patterns/1,
    clause_body/1,
    clause_guard/1,
    type/1
]).

-export([type_check/2, addFuncSkeltons/2]).

%% PRINT Debugging macro%%
-ifndef(PRINT).
-define(PRINT(Var), io:format("DEBUG: ~p:~p - ~p~n~n ~p~n~n", [?MODULE, ?LINE, ??Var, Var])).
-endif.

%% BDTC - Start %%

% Helpers for testing

terr(Reason) -> erlang:error("Type Error: " ++ Reason).

% showList([]) -> "";
% showList(List) ->
%     ListToShow = io_lib:format("~p",[List]),
%     lists:flatten(ListToShow).

% showAny(Val) ->
%     ListToShow = io_lib:format("~p",[Val]),
%     lists:flatten(ListToShow).

% intToChar(Val) ->
%     L = Val + 65,
%     io_lib:format("~c", [L]).

% intToSmallChar(Val) ->
%     L = Val + 97,
%     io_lib:format("~c", [L]).

subset([A|As], B) ->
    case lists:member(A, B) of
        true  -> subset(As, B);
        false -> false
    end;
subset (_A, _B) -> true.

showType(Ty) ->
    Res = hm:pretty(Ty). %,
    % " ".
    % ?PRINT(Ty),
    % {TyStr, _} = showType_(Ty, init_meta()),
    % TyStr.

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
prune(Env, {funt, _, ArgTys, RetT}) ->
    {Env_L, PT_L} = prune_list(Env, ArgTys),
    {Env_R, PT_R} = prune(Env_L, RetT),
    {Env_R, hm:funt(PT_L, PT_R, 0)};
prune(Env, {tcon, _,Left, ArgTys}) ->
    {Env_L, PT_L} = prune(Env, Left),
    {Env_R, PT_R} = prune_list(Env_L, ArgTys),
    {Env_R, hm:tcon(PT_L, PT_R, 0)};
prune(Env, {forall, Name, _, Body}) ->
    {Env_, PT} = prune(Env, Body),
    {Env_, {forall, Name, [], PT}};
prune(Env, T) -> {Env, T}.

prune_list(Env, Types) ->
    {E_, PL} = lists:foldr(fun(T, {Ei, AccTy}) ->
        {Ei_, PTy} = prune(Ei, T),
        {Ei_, [PTy| AccTy]}
    end,
    {Env, []}, Types),
    {E_, PL}.

applyEnv(Env, {tMeta, L, Id, _, _, _}) ->
    % ?PRINT(Id),
    {tMeta, L, Id, Tvs, Type, Mono} = env:get_meta(Env, Id),
    case Type of
        null -> {tMeta, L, Id, Tvs, Type, Mono};
        _    -> {tMeta, L, Id, Tvs, applyEnv(Env, Type), Mono}
    end;
applyEnv(Env, {funt, L, Args, Ret}) ->
    As_ = lists:map(fun(A) -> applyEnv(Env, A) end, Args),
    hm:funt(As_, applyEnv(Env, Ret), L);
applyEnv(Env, {tcon, L, Name, Args}) -> 
    As_ = lists:map(fun(A) -> applyEnv(Env, A) end, Args),
    % We are not applying on the name of the tcon
    hm:tcon(Name, As_, L);
applyEnv(Env, {forall, Name, Ps, Body}) -> 
    {forall, Name, Ps, applyEnv(Env, Body)};
applyEnv(_, T) -> T.
% applyEnv(_, T) -> ?PRINT(T), T.

applyEnvAndPrune(Env, Type) ->
    prune(Env, applyEnv(Env, Type)).

% flattenApp({app, Left, Right}) ->
%     {T, Args} = flattenApp (Left),
%     {T, Args ++ [Right]};
%     % {T, [Right] ++ Args};
% flattenApp(T) -> {T, []}.

% Subtyping
checkSolution(Env, T, T) -> {Env, false};
checkSolution(Env, {tMeta, _, Id_m, _, _, _} = M, {tMeta, _, Id_t, _, _, _}) ->
% todo     if (m.mono) t.mono = true;
    {tMeta, _, Id_m, Tvs_m, _, Mono_m} = env:get_meta(Env, Id_m),
    {tMeta, L_t, Id_t, Tvs_t, Type_t, _} = env:get_meta(Env, Id_t),
    Env_ = case Mono_m of
        true -> env:set_meta(Env, Id_t, {tMeta, L_t, Id_t, Tvs_t, Type_t, true});
        false -> Env
    end,
    case Type_t of
        null -> checkSolution(Env_, M, Type_t);
        _    -> {Env_, subset(Tvs_m, Tvs_t)}
    end;
checkSolution(Env, M, {funt, _, Args, Ret}) ->
    {Env_, LRes} = checkSolutionList(Env, M, Args),
    {Env__, RRes} = checkSolution(Env_, M, Ret),
    {Env__, LRes and RRes};
checkSolution(Env, M, {tcon, _, Name, Args}) ->
    {Env_, LRes} = checkSolution(Env, M, Name),
    {Env__, RRes} = checkSolutionList(Env_, M, Args),
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

checkSolutionList(Env, M, Args) ->
    lists:foldr(fun(Arg, {Ei, Res}) ->
        {Ei_, Res_} = checkSolution(Ei, M, Arg),
        {Ei_, Res_ and Res}
    end, {Env, true} ,Args).

%% Clean up unify to use tvar functions
unify(Env, _Tvs, A, A) -> {Env, A};
unify(Env, _Tvs, {bt, L, BT}, {bt, L, BT}) ->
    {Env, {bt, L, BT}};
unify(Env, _Tvs, {tvar, _, Name_A}, {tvar, _, Name_B}) when Name_A == Name_B ->
    {Env, hm:tvar(Name_A, 0)};
unify(Env, Tvs, {funt, _, Args_A, Ret_A}, {funt, _, Args_B, Ret_B}) ->
    {Env_, Args} = unifyList(Env, Tvs, Args_A, Args_B),
    {Env__, Ret_U} = unify(Env_, Tvs, Ret_A, Ret_B),
    {Env__, hm:funt(Args, Ret_U, 0)};
unify(Env, _Tvs, {tcon, _, "tuple", _} = T, {tcon, _, "tuple", []}) ->
    %% Handle the case where empty 'tuple()' type
    %% used for generic and dynamic n-sized tuples.
    {Env, T};
unify(Env, _Tvs, {tcon, _, "tuple", []}, {tcon, _, "tuple", _} = T) ->
    %% Handle the case where empty 'tuple()' type
    %% used for generic and dynamic n-sized tuples.
    {Env, T};
unify(Env, Tvs, {tcon, _, "union", _} = A, B) ->
    %% union subtype unify
    % ?PRINT(A),
    % ?PRINT(B),
    case unionSubsume(Env, Tvs, A, B) of 
        uni_failed -> unifyFailed(A, B);
        Res -> Res
    end;
unify(Env, Tvs, A, {tcon, _, "union", _} = B) ->
    % ?PRINT(A),
    % ?PRINT(B),
    case unionSubsume(Env, Tvs, A, B) of 
        uni_failed -> unifyFailed(A, B);
        Res -> Res
    end;
unify(Env, Tvs, {tcon, _, Name, Args_A}, {tcon, _, Name, Args_B}) ->
    % {Env_1, Name} = unify(Env, Tvs, Name_A, Name_B), 
    % TODO: VR do we need this at all?
    {Env_2, Args} = unifyList(Env, Tvs, Args_A, Args_B),
    {Env_2, hm:tcon(Name, Args, 0)};
unify(Env, Tvs, {forall, Name_A, _, Body_A}=A, {forall, Name_A, _, Body_A}=B) ->
    Sk = hm:freshTSkol(),
    {tSkol, _, SkId} = Sk,
    unify(Env, [SkId] ++ Tvs, hm:openTForall(A, Sk), hm:openTForall(B, Sk));
unify(Env, Tvs, {tMeta, _, Id_A, _, _, _}, {tMeta, _, Id_B, _, _, _}) ->
    A = env:get_meta(Env, Id_A),
    B = env:get_meta(Env, Id_B),
    unifyTMeta(Env, Tvs, A, B);
unify(Env, Tvs, {tMeta, _, Id_m, _, _, _}, B) ->
    A = env:get_meta(Env, Id_m),
    unifyTMeta(Env, Tvs, A, B);
unify(Env, Tvs, A , {tMeta, _, Id_m, _, _, _}) ->
    B = env:get_meta(Env, Id_m),
    % ?PRINT(A),
    % ?PRINT(B),
    % TODO: Do we need to swap now?
    % unifyTMeta(Env, Tvs, B, A);
    unifyTMeta(Env, Tvs, A, B);
unify(Env, _Tvs, A, B) ->
    {Env_1, A_} = applyEnvAndPrune(Env, A),
    {Env_2, B_} = applyEnvAndPrune(Env_1, B),
    case hm:isSubType(A_, B_) of
        true-> {Env_2, A};
        false ->
            % ?PRINT(A_),
            % ?PRINT(B_),
            io:fwrite("unify failed with types "),
            showType(A_),
            io:fwrite(" :=: "),
            showType(B_),
            io:fwrite("~n"),
            terr("unify failed!")
    end.

unifyFailed(A, B) -> 
    ?PRINT(A),
    ?PRINT(B),
    io:fwrite("union-unify failed with types "),
    showType(A),
    io:fwrite(" :=: "),
    showType(B),
    io:fwrite("~n"),
    terr("unify failed!").

% A <: (B|C) => (A <: B) or (A <: C)
% handle empty tmeta
unionSubsume(Env, Tvs, {tMeta, _, Id_m, _, _, _}= TM, {tcon, _, "union", _}=RU) ->
    {tMeta, L, Id_m, Tvs_m, Type, Mono} = env:get_meta(Env, Id_m),
    case Type of
        %% Replace incase of empty TMeta
        null ->
            Env_1 = update_tmeta_type(Env, TM, RU),
            {Env_1, {tMeta, L, Id_m, Tvs_m, RU, Mono}};
        Type -> unionSubsume(Env, Tvs, Type, RU)
    end;
unionSubsume(Env, Tvs, {tcon, _, "union", _}=LU, {tMeta, _, Id_m, _, _, _}= TM) ->
    {tMeta, L, Id_m, Tvs_m, Type, Mono} = env:get_meta(Env, Id_m),
    % ?PRINT(Id_m),
    % ?PRINT(Type),
    % ?PRINT(Types),
    % trySubsumeLeftUnion(Env, Tvs, TM, Types);
    case Type of
        %% Replace incase of empty TMeta
        null ->
            Env_1 = update_tmeta_type(Env, TM, LU),
            {Env_1, {tMeta, L, Id_m, Tvs_m, LU, Mono}};
        Type -> unionSubsume(Env, Tvs, LU, Type)
    end;
unionSubsume(Env, Tvs, {tcon, _, "union", L_Types}=L, {tcon, _, "union", _}=R) ->
    Env_ = lists:foldr(fun(Ty, Ei) ->
        Ei_ = case unionSubsume(Ei, Tvs, Ty, R) of
            uni_failed -> unifyFailed(Ty, R);
            {REi, A}   -> REi
        end,
        Ei_
    end, Env, L_Types),
    {Env_, L};
unionSubsume(Env, Tvs, A, {tcon, _, "union", Types}) ->
    trySubsumeRightUnion(Env, Tvs, A, Types);
unionSubsume(Env, Tvs, {tcon, _, "union", Types}, R) ->
    trySubsumeLeftUnion(Env, Tvs, R, Types).

trySubsumeRightUnion(_Env, _Tvs, _A, []) ->
    uni_failed;
trySubsumeRightUnion(Env, Tvs, A, [H | Tail]) ->
    case tryUnify(Env, Tvs, A, H) of
        uni_failed -> trySubsumeRightUnion(Env, Tvs, A, Tail);
        Res -> Res
    end.

trySubsumeLeftUnion(Env, Tvs, A, Types) ->
    Env_ = lists:foldr(fun(Ty, Ei) ->
        {Ei_, A_} = unify(Ei, Tvs, Ty, A),
        Ei_
    end, Env, Types),
    {Env_, A}.

trySubsumeBothUnion(Env, Tvs, A, Types) ->
    Env_ = lists:foldr(fun(Ty, Ei) ->
        {Ei_, A_} = unify(Ei, Tvs, Ty, A),
        Ei_
    end, Env, Types),
    {Env_, A}.

tryUnify(Env, Tvs, T1, T2) ->
    try subsume(Env, Tvs, T1, T2) of
        Res -> Res
    catch
        _:_ -> uni_failed
    end.

unifyList(Env, Tvs, As, Bs) ->
    % ?PRINT(As),
    % ?PRINT(Bs),
    lists:foldl(fun({A, B}, {Ei, Ts}) ->
        {Ei_, T} = unify(Ei, Tvs, A, B),
        {Ei_, Ts ++ [T]}
    end,
    {Env, []}, lists:zip(As, Bs)).

unifyTMeta(Env, _Tvs, M, M) -> {Env, M};
unifyTMeta(Env, Tvs, {tMeta, _, _, _, Type, _}, T) when Type =/= null ->
    unify(Env, Tvs, Type, T);
unifyTMeta(Env, Tvs, M, {tMeta, _, _, _, Type, _}) when Type =/= null ->
    unify(Env, Tvs, M, Type);
unifyTMeta(Env, _Tvs, {tMeta, L, Id, Tvs, null, Mono}, {bt, _, term}=T) ->
    TM = {tMeta, L, Id, Tvs, T, Mono},
    Env_ = env:set_meta(Env, Id, TM),
    {Env_, TM};
unifyTMeta(Env, _Tvs, {tMeta, L, Id, Tvs, null, Mono}, {bt, _, any}=T) ->
    TM = {tMeta, L, Id, Tvs, T, Mono},
    Env_ = env:set_meta(Env, Id, TM),
    {Env_, TM};
% Not sure we need this at all
unifyTMeta(Env, _Tvs, {bt, _, term}=T, {tMeta, L, Id, Tvs, null, Mono}) ->
    TM = {tMeta, L, Id, Tvs, T, Mono},
    Env_ = env:set_meta(Env, Id, TM),
    {Env_, TM};
unifyTMeta(Env, _Tvs, {bt, _, any}=T, {tMeta, L, Id, Tvs, null, Mono}) ->
    TM = {tMeta, L, Id, Tvs, T, Mono},
    Env_ = env:set_meta(Env, Id, TM),
    {Env_, TM};
% This is to order tMeta based on dependency.
unifyTMeta(Env, Tvs, {tMeta, _, Id_F, _, _, _}, {tMeta, _, Id_S, _, _, _}) ->
    {M, T} = orderTMeta(Env, Id_F, Id_S),
    {tMeta, L, Id, _, _, Mono}=M,
    {Env_, Res} = checkSolution(Env, M, T),
    case Res of
        true  ->
            TM = {tMeta, L, Id, Tvs, T, Mono},
            Env__ = env:set_meta(Env_, Id, TM),
            {Env__, TM};
        false ->
            ?PRINT(M),
            ?PRINT(T),
            io:fwrite("unify meta variable failed with types "),
            showType(M),
            io:fwrite(" :=: "),
            showType(T),
            io:fwrite("~n"),
            terr("unify meta variable failed!")
end;
% TODO: Not sure we can simply assign this but , Fixed based on old solution
% A <: (A|B) how do we unify this meta relation?
% A cannot say its same as A -> (A|B) which will do a cyclic dependency.
% So going with 
unifyTMeta(Env, Tvs, {tMeta, L, Id, _, _, Mono} = M, T) ->
    {Env_, Res} = checkSolution(Env, M, T),
    case Res of
        true  ->
            TM = {tMeta, L, Id, Tvs, T, Mono},
            Env__ = env:set_meta(Env_, Id, TM),
            {Env__, TM};
        false -> checkMetaSubtypes(Env_, M, T)
    end;
unifyTMeta(Env, Tvs, M, {tMeta, L, Id, _, _, Mono} = T) ->
    {Env_, Res} = checkSolution(Env, M, T),
    case Res of
        true  ->
            TT = {tMeta, L, Id, Tvs, M, Mono},
            Env__ = env:set_meta(Env_, Id, TT),
            {Env__, TT};
        false -> checkMetaSubtypes(Env_, M, T)
    end;
unifyTMeta(_Env, _Tvs, M, T) ->
    % Nothing matches!
    ?PRINT(M),
    ?PRINT(T).

checkMetaSubtypes(Env, M, T) ->
    {Env_1, M_} = applyEnvAndPrune(Env, M),
    {Env_2, T_} = applyEnvAndPrune(Env_1, T),
    case hm:isSubType(M_, T_) of
        true ->
            % Todo if the unification with subtype we just ignore.
            % Also do we need to check the other direction
            {Env_2, M_};
        false ->
            io:fwrite("unify meta variable failed with types "),
            showType(M),
            io:fwrite(" :=: "),
            showType(T),
            io:fwrite("~n"),
            terr("unify meta variable failed!")
    end.

orderTMeta(Env, Id_F, Id_S) ->
    case Id_F > Id_S of
        true ->
            {env:get_meta(Env, Id_F), env:get_meta(Env, Id_S)};
        false ->
            {env:get_meta(Env, Id_S), env:get_meta(Env, Id_F)}
    end.

subsume(Env, Tvs, Inf, {forall,_, _, _}=Ty) ->
    Sk = hm:freshTSkol(),
    {tSkol, _, SkId} = Sk,
    unify(Env, [SkId] ++ Tvs, Inf, hm:openTForall(Ty, Sk));
subsume(Env, Tvs, {forall, _, _, _}=Inf, Ty) ->
    {Env_, M} = hm:freshTMeta(Env, Tvs, 0),
    unify(Env_, Tvs, hm:openTForall(Inf, M), Ty);
subsume(Env, Tvs, Inf, Ty) ->
    % ?PRINT(Inf),
    % ?PRINT(Ty),
    unify(Env, Tvs, Inf, Ty).

% Inference/ Synthesis
% synth(Env, _Tvs, {const, bool}) ->
%     {Env, tBool()};
% synth(Env, _Tvs, {var, Name}) ->
%     case env:lookup(Name, Env) of
%         not_found -> terr("undefined var : " ++  Name);
%         Ty -> {Env, Ty}
%     end;
% synth(Env, Tvs, {ann, Term, Type}) ->
%     check(Env, Tvs, Term, Type);
% synth(Env, Tvs, {app, _Left, _Right}=Term) ->
%     {FT, As} = flattenApp(Term),
%     {Env_, Ty} = synth(Env, Tvs, FT),
%     synth_call(Env_, Tvs, Ty, As, null, []);
% synth(Env, Tvs, {abs, Name, Body}) ->
%     {Env_1, A} = hm:freshTMeta(Env, Tvs, true, 0),
%     {Env_2, B} = hm:freshTMeta(Env_1, Tvs, 0),
%     {Env_3, _} = check(env:extend(Name, A, Env_2), Tvs, Body, B),
%     {Env_3, hm:funt([A], B, 0)};
% synth(Env, Tvs, {func, FName, VName, Body}) ->
%     {Env_1, A} = hm:freshTMeta(Env, Tvs, true, 0),
%     {Env_2, B} = hm:freshTMeta(Env_1, Tvs, 0),
%     FT = hm:funt([A], B, 0),
%     Env_3 = env:extend(FName, FT, Env_2),
%     {Env_4, _} = check(env:extend(VName, A, Env_3), Tvs, Body, B),
%     {Env_4, hm:funt([A], B, 0)};
% synth(Env, Tvs, {if_else, Cond, TB, FB}) ->
%     {Env_1, A} = hm:freshTMeta(Env, Tvs, 0),
%     {Env_2, _} = check(Env_1, Tvs, Cond, tBool()),
%     {Env_3, _} = check(Env_2, Tvs, TB, A),
%     {Env_4, _} = check(Env_3, Tvs, FB, A),
%     {Env_4, A};
% synth(_, _, Term) ->
%     terr("cannot synth : " ++ showAny(Term)).

synth_call(Env, Tvs, {forall, _, _, _} = Ty, As, ExpectedType, Acc) ->
    {Env_, M}= hm:freshTMeta(Env, Tvs, 0),
    Opened = hm:openTForall(Ty, M),
    synth_call(Env_, Tvs, Opened, As, ExpectedType, Acc);
synth_call(Env, Tvs, {funt, _, ArgTs, RetTy}, As, ExpectedType, Acc) when length(As) > 0 ->
    Acc_ = lists:foldl(fun({A, AT}, Ac)->
        Ac ++ [{A, AT}]
    end, Acc, lists:zip(As, ArgTs)),
    synth_call(Env, Tvs, RetTy, [], ExpectedType, Acc_);
synth_call(Env, Tvs, {tMeta, _, Id_m, _, _, _}, As, ExpectedType, Acc) when length(As) > 0 ->
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
            synth_call(Env_, Tvs, B, AsTail, ExpectedType, Acc_);
        Valid -> synth_call(Env, Tvs, Valid, As, ExpectedType, Acc)
    end;
synth_call(_, _, SynthFailTy, As, _, _) when length(As) > 0 ->
    terr("synth_call failed, not a function type: " ++ showType(SynthFailTy));
synth_call(Env, Tvs, Ty, _As, ExpectedType, Acc) ->
    Env__ = case ExpectedType of
        null    ->
            pickAndCheckArgs(Env, Tvs, Acc);
        _       ->
            {Env_, _T} = unify(Env, Tvs, Ty, ExpectedType),
            pickAndCheckArgs(Env_, Tvs, Acc)
    end,
    {Env__, Ty}.

% Bug to check
pickAndCheckArgs(Env, _, []) -> Env;
pickAndCheckArgs(Env, Tvs, Acc) ->
    {Env_1, {{Tm, TmTy}, RestAcc}} = pickArg(Env, Acc),
    {Env_2, _T} = bd_check(Env_1, Tvs, Tm, TmTy),
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

% check(Env, Tvs, Term, {tMeta, _, Id_m, _, _, _} = Ty) ->
%     {tMeta, _, Id_m, _, Type, _} = env:get_meta(Env, Id_m),
%     case Type of
%         null -> synthAndSubsume(Env, Tvs, Term, Ty);
%         ValidType -> check(Env, Tvs, Term, ValidType)
%     end;
% check(Env, Tvs, Term, {forall, _, _, _} = Ty) ->
%     Sk = hm:freshTSkol(0),
%     {tSkol, _, SkId} = Sk,
%     check(Env, [SkId] ++ Tvs, Term, hm:openTForall(Ty, Sk));
% check(Env, Tvs, {abs, Name, Body}, {funt, _, [Left], Right}) ->
%     check(env:extend(Name, Left, Env), Tvs, Body, Right);
% check(Env, Tvs, {app, _, _} = Term, Ty) ->
%     {FT, As} = flattenApp(Term),
%     {Env_, FTy} = synth(Env, Tvs, FT),
%     synth_call(Env_, Tvs, FTy, As, Ty, []);
% check(Env, Tvs, {if_else, Cond, TB, FB}, Ty) ->
%     {Env_1, _} = check(Env, Tvs, Cond, tBool()),
%     {Env_2, _} = check(Env_1, Tvs, TB, Ty),
%     {Env_3, _} = check(Env_2, Tvs, FB, Ty),
%     {Env_3, Ty};
% check(Env, Tvs, Term, Ty) ->
%     synthAndSubsume(Env, Tvs, Term, Ty).

%% BDTC - End %%

synthAndSubsume(Env, Tvs, Term, Ty) ->
    {Env_, Inf} = btc_synth(Env, Tvs, Term),
    % ?PRINT(Inf),
    % printType(Env_, Inf),
    % ?PRINT(Ty),
    % printType(Env_, Ty),
    subsume(Env_, Tvs, Inf, Ty).

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
    ?PRINT(FunQName),
    % ?PRINT(SpecFT),
    UdtInTy = hm:inplaceUDT(Env, SpecFT),
    % ?PRINT(UdtInTy),
    GenSpecT = hm:generalizeSpecT(Env, UdtInTy),
    % ?PRINT(GenSpecT),
    {Env_, Type} = bd_check(Env, [], F, GenSpecT),
    {Env, Type}.
    % case Result of
    %     false -> erlang:error({type_error
    %                            , "Check failed for the function:: " ++ util:to_string(FunQName)});
    %     true  -> true
    % end.

do_btc_infer(Env, F) ->
    FunQName = util:getFnQName(F),
    ?PRINT(FunQName),
    {SEnv, STy} = btc_synth(Env, [], F),
    % ?PRINT(env:get_meta_map(SEnv)),
    % ?PRINT(STy),
    Ty_ = applyEnv(SEnv, STy),
    % ?PRINT(Ty_),
    % ?PRINT(env:get_meta_map(Env_)),
    {Env_, PTy} = prune(SEnv, Ty_),
    % ?PRINT(PTy),
    % io:fwrite("~p :: ",[FunQName]),
    % showType(PTy),
    % io:fwrite("~n",[]),
    ExtendedEnv = env:extend(FunQName, PTy, Env),
    % ?PRINT(Env_),
    {ExtendedEnv, PTy}.

bd_check(Env, Tvs, Term, {tMeta, _, Id_m, _, _, _} = Ty) ->
    {tMeta, _, Id_m, _, Type, _} = env:get_meta(Env, Id_m),
    case Type of
        null -> synthAndSubsume(Env, Tvs, Term, Ty);
        ValidType -> bd_check(Env, Tvs, Term, ValidType)
    end;
%%%%%%%%%%%%%%%%%check with special cases%%%%%%%%%%%%%%%%%
bd_check(Env, _Tvs, {var, _L, '_'}, Type) ->
    {Env, Type};
bd_check(Env, Tvs, {var, L, X}, Type) ->
    case env:is_bound(X, Env) of
        true  ->
            VarT = lookup(X, Env, L),
            subsume(Env, Tvs, VarT, Type);
        false ->
            VarT = hm:replaceLn(Type, L),
            Env_ = env:extend(X, VarT, Env),
            {Env_, VarT}
    end;
% Support list of union types
bd_check(Env, Tvs, {cons, _, Head, Tail}, Type) ->
    {Env_1, _TailTy} = bd_check(Env, Tvs, Tail, Type),
    ElemTy = hm:getListType(Env_1, Type),
    {Env_2, _HT} = bd_check(Env_1, Tvs, Head, ElemTy),
    {Env_2, Type};
%%%%%%%%%%%%%%%%%check with special cases%%%%%%%%%%%%%%%%%
bd_check(Env, Tvs, Term, {forall, {tvar,L,_}, _, _} = Ty) ->
    Sk = hm:freshTSkol(L),
    % ?PRINT(Sk),
    {tSkol, _, SkId} = Sk,
    Opened = hm:openTForall(Ty, Sk),
    bd_check(Env, [SkId] ++ Tvs, Term, Opened);
bd_check(Env, Tvs, {clause, L, _, _, _}=Clause, {funt, _, ArgTys, RetTy} = FT) ->
    ClausePatterns = clause_patterns(Clause),
    ClauseBody = clause_body(Clause),
    Env_ = lists:foldl(fun({P, T}, Ei)->
        % env:extend(P, T, Ei)
        {Ei_, _} = bd_check(Ei, Tvs, P, T),
        Ei_
    end, Env, lists:zip(ClausePatterns, ArgTys)),
    Env_2 = inferClauseBody(Env_, Tvs, ClauseBody),
    bd_check(Env_2, Tvs, lists:last(ClauseBody), RetTy);
bd_check(Env, Tvs, {call, L, F, Args}= Term, Ty) ->
    {Env_0, FTy}= synthFnCall(Env, F, length(Args)),
    Gen_FT = genFnCallTy(Env, FTy),
    synth_call(Env_0, Tvs, Gen_FT, Args, Ty, []);
bd_check(Env, Tvs, Node, Type) ->
        case type(Node) of
            Fun when Fun =:= function; Fun =:= fun_expr ->
                Clauses = case Fun of
                    function -> function_clauses(Node);
                    fun_expr -> ?PRINT(Node), fun_expr_clauses(Node)
                end,
                ClausesCheckRes = lists:map(fun(C) -> bd_check(Env, Tvs, C, Type) end, Clauses),
                % ?PRINT(ClausesCheckRes),
                % Result = lists:foldl(
                %     fun({_Env, Res, _T}, AccRes) ->
                %         AccRes and Res
                %     end, true, ClausesCheckRes),
                {Env, Type};
            _ ->
                % io:fwrite("BTC check is not supported, so using synth and subsume ~n"),
                % ?PRINT(Node),
                % ?PRINT(Type),
                synthAndSubsume(Env, Tvs, Node, Type)
        end.

-spec btc_synth(hm:env(), [any()], erl_syntax:syntaxTree()) ->
    {hm:env(), hm:type()}.
btc_synth(Env, _Tvs, {integer, L, _}) ->
    Inferred = hm:bt(integer, L),
    {Env, Inferred};
btc_synth(Env, _Tvs, {string, L,_}) ->
    Inferred = hm:tcon("list", [hm:bt(char,L)],L),
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
btc_synth(Env, Tvs, {nil, L}) ->
    {Env_1, A} = hm:freshTMeta(Env, Tvs, L),
    ListType = hm:tcon("list", [A], L),
    {Env_1, ListType};
btc_synth(Env, Tvs, {cons, L, Head, Tail}) ->
    {Env_1, HType} = btc_synth(Env, Tvs, Head),
    {Env_2, TType} = btc_synth(Env_1, Tvs, Tail),
    % generate a fresh "list"
    %% Not sure we need to create new fresh meta list %%
    % {Env_3, A} = hm:freshTMeta(Env_2, Tvs, L),
    LType = hm:tcon("list", [HType], L),
    % {Env_4, _AU} = subsume(Env_3, Tvs, A, HType),
    {Env_5, _LU} = subsume(Env_2, Tvs, LType, TType),
    {Env_5, LType};
btc_synth(Env, Tvs, {tuple, L, Es}) ->
    {Env_, TTs} = lists:foldl(
        fun(X, {Ei, AccT}) -> 
            {Ei_, T} = btc_synth(Ei, Tvs, X),
            {Ei_, AccT ++ [T]}
        end, {Env,[]}, Es),
    TupleType = hm:tcon("tuple", TTs, L),
    {Env_, TupleType};
btc_synth(Env, _Tvs, {map, L, []}) ->
    AnyToAny = hm:tcon("key-value",[hm:bt(any, L), hm:bt(any, L)],L),
    {Env, hm:tcon("map", [AnyToAny], L)};
btc_synth(Env, _Tvs, {map, L, Kvs}) ->
    ?PRINT(Kvs),
    AnyToAny = hm:tcon("key-value",[hm:bt(any, L), hm:bt(any, L)],L),
    {Env, hm:tcon("map", [AnyToAny], L)};
btc_synth(Env, Tvs, {var, L, '_'}) ->
    hm:freshTMeta(Env, Tvs, true, L);
btc_synth(Env, Tvs, {var, L, X}) ->
    case env:is_bound(X, Env) of
        true  ->
            T = lookup(X, Env, L),
            {Env, T};
        false ->
            {Env_, A} = hm:freshTMeta(Env, Tvs, true, 0),
            {env:extend(X, A, Env_), A}
    end;
    % {op,11,'not',{var,11,'X'}}
btc_synth(Env, Tvs, {op, L, UOp, E}) ->
    OpType = lookup(UOp, Env, L),
    {Env_, OpenedType} = open_op_type(Env, Tvs, OpType),
    Arg1Type = hd(hm:get_fn_args(OpenedType)),
    RetType = hm:get_fn_rt(OpenedType),
    {Env1, _T1} = bd_check(Env_, Tvs, E, Arg1Type),
    {Env1, RetType};
btc_synth(Env, Tvs, {op, L, BOp, E1, E2}) ->
    OpType = lookup(BOp, Env, L),
    {Env_, OpenedType} = open_op_type(Env, Tvs, OpType),
    Arg1Type = hd(hm:get_fn_args(OpenedType)),
    Arg2Type = lists:last(hm:get_fn_args(OpenedType)),
    RetType = hm:get_fn_rt(OpenedType),
    % ?PRINT(Arg1Type),
    % ?PRINT(RetType),
    {Env1, _T1} = bd_check(Env_, Tvs, E1, Arg1Type),
    % ?PRINT(_T1),
    {Env2, _T2} = bd_check(Env1, Tvs, E2, Arg2Type),
    % ?PRINT(RetType),
    {Env2, RetType};
btc_synth(Env, Tvs, {call,L,F,Args}) ->
    {Env_0, FT }= synthFnCall(Env, F, length(Args)),
    % {Env_0, FT_} = applyEnvAndPrune(Env, FT),
    % ?PRINT(FT),
    {Env_1, Fresh_FT} = genAndOpenFnCallTy(Env_0, Tvs, FT),
    % ?PRINT(Fresh_FT),
    {Env_2, OpenedType} = open_op_type(Env_1, Tvs, Fresh_FT),
    ArgTypes = hm:get_fn_args(OpenedType),
    {Env_3, ArgTys} = lists:foldl(
        fun({Arg, ArgTy}, {Ei, ATs}) ->
            % ?PRINT(Arg),
            % ?PRINT(ArgTy),
            {Ei_, T} = bd_check(Ei, Tvs, Arg, ArgTy),
            {Ei_, ATs ++ [T]}
        end
        , {Env_2,[]}, lists:zip(Args, ArgTypes)),
    RetType = hm:get_fn_rt(OpenedType),
    % printType(Env_3, RetType),
    {Env_3, RetType};
btc_synth(Env, Tvs, {match, L, LNode, RNode} = Node) ->
    {Env_1, LTy} = btc_synth(Env, Tvs, LNode),
    {Env_2, RTy} = btc_synth(Env_1, Tvs, RNode),
    subsume(Env_2, Tvs, LTy, RTy);
btc_synth(Env, _Tvs, {'fun',L,{function,X,ArgLen}}) ->
    T = lookup({X,ArgLen}, Env, L),
    {Env, T};
btc_synth(Env, Tvs, {'if',_,Clauses}) ->
    {Env_1, CTs} = btc_synth_clauses(Env, Tvs, Clauses),
    EnvUnionEn = env:enableClauseUnion(Env_1),
    {Env_2, CT} = subsume_clauses(EnvUnionEn, Tvs, CTs),
    EnvUnionDis = env:disableClauseUnion(Env_2),
    RetType = hm:get_fn_rt(CT),
    {EnvUnionDis, RetType};
btc_synth(Env, Tvs, {'fun',L,{function,X,ArgLen}}=Term) ->
    ?PRINT(Term),
    T = lookup({X,ArgLen},Env,L),
    {Env, T};
btc_synth(Env, Tvs, {'case',_,Expr,Clauses}) ->
    {Env_1, EType} = btc_synth(Env, Tvs, Expr),
    {Env_2, CTs} = btc_synth_clauses(Env_1, Tvs, Clauses),
    EnvUnionEn = env:enableClauseUnion(Env_2),
    {Env_3, CT} = subsume_clauses(EnvUnionEn, Tvs, CTs),
    EnvUnionDis = env:disableClauseUnion(Env_3),
    % EnvUnionEn
    Arg1Type = hd(hm:get_fn_args(CT)),
    {Env_4, _} = subsume(EnvUnionDis, Tvs, EType, Arg1Type),
    RetType = hm:get_fn_rt(CT),
    {Env_4, RetType};
btc_synth(Env, Tvs, {'receive',_,Clauses}) ->
    {Env_1, CTs} = btc_synth_clauses(Env, Tvs, Clauses),
    {Env_2, CT} = subsume_clauses(Env_1, Tvs, CTs),
    RetType = hm:get_fn_rt(CT),
    {Env_2, RetType};
btc_synth(Env, Tvs, {clause, L, _, _, _}=Clause) ->
    ClausePatterns = clause_patterns(Clause),
    ClauseGuards = clause_guard(Clause),
    Env_ = guardBoolCheck(Env, Tvs, ClauseGuards),
    ClauseBody = clause_body(Clause),
    % {Env_1, A} = btc_synth(Env, Tvs, hd(ClausePatterns)),
    {Env_1, As} = synth_clause_patterns(Env_, Tvs, ClausePatterns),
    {Env_2, B} = hm:freshTMeta(Env_1, Tvs, L),
    % Env_3 = env:extend(Name, A, Env_2),
    Env_3 = synth_clause_body(Env_2, Tvs, ClauseBody),
    LstBdy = lists:last(ClauseBody),
    % ?PRINT(LstBdy),
    {Env_4, _} = bd_check(Env_3, Tvs, LstBdy, B),
    FT = hm:funt(As, B, L),
    % printType(Env_4, FT),
    % ?PRINT(FT),
    {Env_4, FT};
btc_synth(Env, Tvs, Node) ->
    case type(Node) of
        Fun when Fun =:= function; Fun =:= fun_expr ->
            Clauses = case Fun of
                function -> function_clauses(Node);
                fun_expr -> fun_expr_clauses(Node)
            end,
            % ClausesCheckRes = lists:map(fun(C) -> btc_synth(Env, Tvs, C) end, Clauses),
            {Env_2, CTs} = btc_synth_clauses(Env, Tvs, Clauses),
            % ?PRINT(CTs),
            {Env_3, CT} = subsume_clauses(Env_2, Tvs, CTs),
            % {Env_ , T} = btc_synth(Env, Tvs, hd(Clauses)),
            {Env_3 , CT};
        X ->
            ?PRINT(Node),
            erlang:error({type_error," Cannot synthesize the type of " 
            ++ util:to_string(Node) ++ " with node type "++ util:to_string(X)})
    end.

% % check if the arg patterns are matching.
checkPatterns(Env, Tvs, ClausePatterns, Type) ->
    PatCheckEnv = env:setPatternInf(Env),
    ArgTypes = hm:get_fn_args(Type),
    ArgAndTypes = lists:zip(ClausePatterns, ArgTypes),
    {Env_1, ATypes} = lists:foldl(
        fun({ArgPattern, ArgType},{Ei, Args}) ->
            {Ei_, Arg_} = bd_check(Ei, Tvs, ArgPattern, ArgType),
            {Ei_, Args ++ [Arg_]}
        end, {PatCheckEnv, []}, ArgAndTypes),
    {env:resetPatternInf(Env_1), ATypes}.

% % check if the arg expr has given arg type.
% -spec checkArgType(hm:env(), erl_syntax:syntaxTree(), hm:types()) -> 
%     {hm:env(), boolean(), hm:types()}.
% checkArgType(Env, ArgPattern, ArgType) ->
%     check(Env, ArgPattern, ArgType).

% check if the arg patters are matching.
% given a body of a clause, returns its type
checkClauseBody(Env, Tvs, BodyExprs, Type) ->
    % TODO: We have to add support for let recursively here
    EnvUnionEn = env:enableClauseUnion(Env),
    Env_ = lists:foldr(fun(Expr, Ei) ->
        {Ei_, _} = btc_synth(Ei, Tvs, Expr),
        Ei_
    end, EnvUnionEn, lists:droplast(BodyExprs)),
    EnvUnionDis = env:disableClauseUnion(Env_),
    Last = lists:last(BodyExprs),
    bd_check(EnvUnionDis, Tvs, Last, Type).

inferClauseBody(Env, Tvs, BodyExprs) ->
    % TODO: We have to add support for let recursively here
    EnvUnionEn = env:enableClauseUnion(Env),
    Env_ = lists:foldr(fun(Expr, Ei) ->
        {Ei_, _} = btc_synth(Ei, Tvs, Expr),
        Ei_
    end, EnvUnionEn, lists:droplast(BodyExprs)),
    env:disableClauseUnion(Env_).

% -spec localConstraintSolver(hm:env(), [hm:constraint()], [hm:predicate()]) ->
%     hm:env().
% localConstraintSolver(Env, InfCs, InfPs) -> 
%     Sub = hm:solve(InfCs),
%     Ps = hm:subPs(InfPs, Sub),
%     {Sub_, _RemPs}   = hm:solvePreds(rt:defaultClasses(), Ps),
%     hm:subE(Env, hm:comp(Sub_, Sub)).

synthFnCall(Env,{atom, L, X}, ArgLen) ->
    {Env, lookup({X, ArgLen}, Env, L)};
synthFnCall(Env,{remote,L,{atom,_,Module},{atom,_,X}},ArgLen) ->
    {Env, lookupRemote({X,ArgLen},Env,L,Module)};
synthFnCall(Env, X, ArgLen) ->
    case isFuncVar(X) of
        true ->
            {var, L, FName} = X,
            FT = lookup(FName, Env, L),
            {Env_, HFT} = handleFreshFunc(Env, FT, X, ArgLen),
            applyEnvAndPrune(Env_, HFT); %TODO handle properly
        false ->
            ?PRINT(X),
            erlang:error(type_error, "Function variable without known type")
    end.

handleFreshFunc(Env, {tMeta,_,_,Tvs,null,_} = FT, {var, L, FName}, ArgLen) ->
    {Env_1, SKT} = funcSkelton(Env, ArgLen, L),
    FunQName = {FName, ArgLen},
    {Env_2, FTU} = subsume(Env_1, Tvs, FT, SKT),
    {env:replace_binding(FunQName, SKT, Env_2), SKT};
handleFreshFunc(Env, FT, _, _) -> {Env, FT}.

isFuncVar({var, _, FName}) when is_atom(FName) ->
    % ?PRINT(FName),
    FC = hd(atom_to_list(FName)),
    IsCap = ((FC >= $A) and (FC =< $Z)),
    IsUS = (FC == $_),
    IsUS or IsCap.

genFnCallTy(Env, FnTy) ->
    Fresh_FT = hm:generalizeType(FnTy),
    hm:generalizeSpecT(Env, Fresh_FT).

genAndOpenFnCallTy(Env, Tvs, FnTy) ->
    Gen_FT = genFnCallTy(Env, FnTy),
    open_op_type(Env, Tvs, Gen_FT).

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

lookupRemote(X,Env,L,Module) ->
    case env:lookupRemote(Module, X, Env) of
        undefined   ->
                erlang:error({type_error,util:to_string(X) ++ 
                            " on line " ++ util:to_string(L) ++ 
                            " is not exported by module " ++ util:to_string(Module)});
        na          ->
            {_,ArgLen} = X,
            ArgTypes = lists:map(fun hm:fresh/1, lists:duplicate(ArgLen,L)),
            hm:funt(ArgTypes,hm:fresh(L),L);
        T           -> T
    end.


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

open_op_type(Env, Tvs, {forall, _, C, _} = Ty) ->
    {Env_1, M} = hm:freshTMeta(Env, Tvs, true, 0), % TODO:why true no idea?
    Env_2 = case C of
        [{class, CName, _ }] ->
            CUT = type_class_to_union(CName),
            % ?PRINT(CUT),
            update_tmeta_type(Env_1, M, CUT);
        _ -> Env_1
    end,
    % ?PRINT(Ty),
    Opened = hm:openTForall(Ty, M),
    % ?PRINT(env:get_meta_map(Env_2)),
    % ?PRINT(Opened),
    % ?PRINT(Opened),
    open_op_type(Env_2, Tvs, Opened);
open_op_type(Env, _, OpType) ->
    % ?PRINT(OpType),
    {Env, OpType}.

% open_op_type_Skol(Env, Tvs, {forall, _, C, _} = Ty) ->
%     {Env_1, M} = hm:freshTMeta(Env, Tvs, true, 0), % TODO:why true no idea?
%     Sk = hm:freshTSkol(0),
%     Env_2 = case C of
%         [{class, CName, _ }] ->
%             CUT = type_class_to_union(CName),
%             update_tmeta_type(Env_1, M, CUT);
%         _ -> Env_1
%     end,
%     % ?PRINT(Ty),
%     Opened = hm:openTForall(Ty, M),
%     % ?PRINT(Opened),
%     % ?PRINT(Opened),
%     open_op_type_Skol(Env_2, Tvs, Opened);
% open_op_type_Skol(Env, _, OpType) ->
%     % ?PRINT(OpType),
%     {Env, OpType}.
%     {tSkol, _, SkId} = Sk,
%     check(Env, [SkId] ++ Tvs, Term, hm:openTForall(Ty, Sk));

update_tmeta_type(Env, {tMeta, L, Id_t, Tvs_t, _, Mono}, Type)->
    NewMeta = {tMeta, L, Id_t, Tvs_t, Type, Mono},
    env:set_meta(Env, Id_t, NewMeta).

latest_tmeta_type(Env, {tMeta, _, Id, _, _, _})->
    env:get_meta(Env, Id).

type_class_to_union(CName)->
    CTs = hm:get_all_class_types(CName),
    hm:tcon("union", CTs, 0).

synth_clause_patterns(Env, _, []) ->
    {Env, []};
synth_clause_patterns(Env, Tvs, [P|Ps]) ->
    {Env_1, A} = btc_synth(Env, Tvs, P),
    {Env_2, As} = synth_clause_patterns(Env_1, Tvs, Ps),
    {Env_2, [A|As]}.

%% this is our let
synth_clause_body(Env, Tvs, Body) ->
    lists:foldr(
        fun(Expr, Ei) ->
            {Ei_, _} = btc_synth(Ei, Tvs, Expr),
            Ei_
        end,
        Env, lists:droplast(Body)).

btc_synth_clauses(Env, Tvs, Clauses) ->
    lists:foldr(
        fun(C, {Ei, ATs}) ->
            {Ei_, CT} = btc_synth(Ei, Tvs, C),
            {Ei_, ATs++[CT]}
        end,
        {Env, []}, Clauses).

subsume_clauses(Env, Tvs, ClauseTys) ->
    C_First = hd(ClauseTys),
    lists:foldl(
        fun(C, {Ei, CT}) ->
            case env:canClauseUnion(Env) of
                true  -> unifyClauseWithUnion(Ei, Tvs, CT, C);
                false -> subsume(Ei, Tvs, CT, C)
            end
        end,
        {Env, C_First}, tl(ClauseTys)).

addFuncSkeltons(Env, Functions)->
    FreshEnv = lists:foldl(fun(F,AccEnv) ->
        {Env_, FT} = funcSkelton(AccEnv, F),
        FunQName = util:getFnQName(F), 
        env:extend(FunQName, FT, Env_)
    end, Env, Functions),
    FreshEnv.

funcSkelton(Env, Func)->
    ArgLen = util:getFnArgLen(Func),
    L = util:getLn(Func),
    funcSkelton(Env, ArgLen, L).

funcSkelton(Env, ArgLen, L)->
    {Env_1, ATMs} = lists:foldr(fun(_, {Ei, ArgTs}) ->
        {Ei_, NM} = hm:freshTMeta(Ei, [], false, L),
        {Ei_, ArgTs ++ [NM]}
    end,
    {Env, []},lists:seq(1, ArgLen)),
    {Env_2, RetM} = hm:freshTMeta(Env_1, [], false, L),
    {Env_2, hm:funt(ATMs, RetM, L)}.

guardBoolCheck(Env, Tvs, {tree, disjunction, _, Conjuctions}) ->
    lists:foldr(fun({tree, conjunction, _, Exprs}, Ei) ->
        checkGuardExpr(Ei, Tvs, Exprs)
   end, Env, Conjuctions);
guardBoolCheck(Env, _, none) -> Env.

checkGuardExpr(Env, Tvs, Exprs)->
    lists:foldr(fun(Expr, Ei) ->
        {Env_1, InfT} = btc_synth(env:enableGuardExprEnv(Ei), Tvs, Expr),
        {Env_2, _} = subsume(Env_1, Tvs, InfT, hm:bt(boolean, 0)),
        Env_2
    end, Env, Exprs).

unifyClauseWithUnion(Env, Tvs, {funt, L1, Args1, Ret1}, {funt, L2, Args2, Ret2}) ->
    {Env_1, Args_} = lists:foldl(fun({Arg1, Arg2}, {Ei, As_}) ->
        {Ei_, A_} = unifyWithUnion(Ei, Tvs, Arg1, Arg2),
        {Ei_, As_ ++ [A_]}
    end, {Env, []}, lists:zip(Args1, Args2)),
    {Env_2, Ret_} = unifyWithUnion(Env_1, Tvs, Ret1, Ret2),
    {Env_2, {funt, L1, Args_, Ret_}}.

unifyWithUnion(Env, Tvs, T1, T2) ->
    try subsume(Env, Tvs, T1, T2) of
        Res -> Res
    catch
        _:_ ->
            {Env, {tcon, util:getLn(T1), "union", [T1, T2]}}
    end.

%%%%%%%%%%%%Test & Debug%%%%%%%%%%%%
printType(Env, T) ->
    {_, D_PT} = applyEnvAndPrune(Env, T),
    ?PRINT(D_PT).
%%%%%%%%%%%%Test & Debug%%%%%%%%%%%%

%%%%%%%Removed%%%%%%%%%%%

% -spec btc_check(hm:env(), [any()], erl_syntax:syntaxTree(), hm:type()) ->
%     {hm:env(),  hm:type()}.
% btc_check(Env, Tvs, {integer,L,_}, Type) ->
%     Inf = hm:bt(integer, L),
%     subsume(Env, Tvs, Inf, Type);
% btc_check(Env, Tvs, {string, L,_}, Type) ->
%     Inf= hm:tcon("list", [hm:bt(char,L)],L),
%     subsume(Env, Tvs, Inf, Type);
% btc_check(Env, Tvs, {char, L,_}, Type) ->
%     Inf= hm:bt(char,L),
%     subsume(Env, Tvs, Inf, Type);
% btc_check(Env, Tvs, {float,L,_}, Type) ->
%     Inf = hm:bt(float, L),
%     subsume(Env, Tvs, Inf, Type);
% btc_check(Env, Tvs, {atom,L,X}, Type) ->
%     Inf = case X of
%         B when is_boolean(B) -> hm:bt(boolean, L);
%         _                    -> hm:bt(atom, L)
%     end,
%     subsume(Env, Tvs, Inf, Type);
% btc_check(Env, Tvs, {nil, L}, Type) ->
%     {Env_1, A} = hm:freshTMeta(Env, Tvs, L),
%     ListType = hm:tcon("list", [A], L),
%     subsume(Env_1, Tvs, ListType, Type);
% % btc_check(Env, Tvs, {cons, L, Head, Tail}, Type) ->
% %     % ?PRINT(Head),
% %     % ?PRINT(Tail),
% %     % ?PRINT(Type),
% %     {Env_1, TType} = btc_check(Env, Tvs, Tail, Type),
% %     {Env_2, A} = hm:freshTMeta(Env_1, Tvs, L),
% %     {Env_3, _HT} = btc_check(Env_2, Tvs, Head, A),
% %     LType = hm:tcon("list", [A], L),
% %     % {Env_4, LT} = subsume(Env_3, Tvs, LType, TType),
% %     subsume(Env_3, Tvs, LType, Type);
% %     % subsume(Env_4, Tvs, LT, Type);
% btc_check(Env, Tvs, {cons, L, Head, Tail}, Type) ->
%     ?PRINT(Head),
%     ?PRINT(Tail),
%     {Env_1, TType} = btc_check(Env, Tvs, Tail, Type),
%     ?PRINT(Type),
%     ?PRINT(TType),
%     ElemTy = hm:getListType(Env_1, TType),
%     {Env_2, _HT} = btc_check(Env_1, Tvs, Head, ElemTy),
%     {Env_2, Type};
% btc_check(Env, Tvs, {tuple, L, Es}, Type) ->
%     % TODO verify how it works with proper type
%     {Env_1, MetaTup} = hm:metaTupleTypeOfN(Env, length(Es), L),
%     TTys = hm:getTupleType(Env_1, MetaTup),
%     {Env_2, _TTs} = lists:foldl(
%         fun({E, TT}, {Ei, AccT}) ->
%             {Ei_, T} = btc_check(Ei, Tvs, E, TT),
%             {Ei_, AccT ++ [T]}
%         end, {Env_1,[]}, lists:zip(Es, TTys)),
%     subsume(Env_2, Tvs, MetaTup, Type);
% btc_check(Env, Tvs, {var, L, '_'}, Type) ->
%     % Nothing to check
%     {Env, Type};
% btc_check(Env, Tvs, {var, L, X}, Type) ->
%     case env:is_bound(X, Env) of
%         true  ->
%             VarT = lookup(X, Env, L),
%             subsume(Env, Tvs, VarT, Type);
%             % synthAndSubsume(Env, Tvs, {var, L, X}, Type);
%             % check_type_var(Env, Type, VarT);
%         false ->
%             VarT = hm:replaceLn(Type, L),
%             Env_ = env:extend(X, VarT, Env),
%             {Env_, VarT}
%     end;
% btc_check(Env, Tvs, {call, L, F, Args}, Type) ->
%     FT = synthFnCall(Env, F, length(Args)),
%     {Env_1, OpenedType} = genAndOpenFnCallTy(Env, Tvs, FT),
%     % ?PRINT(OpenedType),
%     ArgTypes = hm:get_fn_args(OpenedType),
%     % Env_ = env:disableGuardExprEnv(Env),
%     {Env_2, ArgTys} = lists:foldl(
%         fun({Arg, ArgTy}, {Ei, ATs}) ->
%             {Ei_, T} = btc_check(Ei, Tvs, Arg, ArgTy),
%             {Ei_, ATs ++ [T]}
%         end
%         , {Env_1, []}, lists:zip(Args, ArgTypes)),
%     RetType = hm:get_fn_rt(OpenedType),
%     subsume(Env_2, Tvs, Type, RetType);
%     % subsume(Env_2, Tvs, RetType, Type); %TODO order we have to fix
% btc_check(Env, Tvs, {match, L, LNode, RNode} = Node, Type) ->
%     case env:isPatternInf(Env) of 
%         false ->
%             {Env_1, LTy} = btc_check(Env, Tvs, LNode, Type),
%             {Env_2, RTy} = btc_check(Env_1, Tvs, RNode, Type),
%             subsume(Env_2, Tvs, LTy, RTy);
%         true ->
%             {Env_1, LTy} = btc_check(Env, Tvs, LNode, Type),
%             {Env_2, RTy} = btc_check(Env_1, Tvs, RNode, Type),
%             subsume(Env_2, Tvs, RTy, LTy)
%     end;
% btc_check(Env, Tvs, {op, L, Op, E1, E2}, Type) ->
%     OpType = lookup(Op, Env, L),
%     % StrippedType = hm:type_without_bound(OpType),
%     {Env_, OpenedType} = open_op_type(Env, Tvs, OpType),
%     Arg1Type = hd(hm:get_fn_args(OpenedType)),
%     Arg2Type = lists:last(hm:get_fn_args(OpenedType)),
%     RetType = hm:get_fn_rt(OpenedType),
%     {Env1, _T1} = btc_check(Env_, Tvs, E1, Arg1Type),
%     {Env2, _T2} = btc_check(Env1, Tvs, E2, Arg2Type),
%     subsume(Env2, Tvs, RetType, Type);
% btc_check(Env, Tvs, {'case',_,Expr,Clauses}, Type) ->
%     {Env_1, EType} = btc_synth(Env, Tvs, Expr),
%     {Env_2, CTs} = btc_synth_clauses(Env_1, Tvs, Clauses),
%     Env_3 = lists:foldr(fun(CT, Ei)->
%         Arg1Type = hd(hm:get_fn_args(CT)),
%         RetType = hm:get_fn_rt(CT),
%         {Ei_1, _} = subsume(Ei, Tvs, Arg1Type, EType),
%         {Ei_2, _} = subsume(Ei_1, Tvs, RetType, Type),
%         Ei_2
%      end, Env_2, CTs),
%     {Env_3, Type};
% btc_check(Env, Tvs, {clause, L, _, _, _}=Clause, Type) ->
%     ClausePatterns = clause_patterns(Clause),
%     ClauseBody = clause_body(Clause),
%     % PatRes = lists:foldl(
%     %     fun(ARes, Res) ->
%     %         ARes and Res
%     %     end, true, PatResults),
%     % ClauseGuards = clause_guard(Node),
%     {Env_1, OpenedType} = open_op_type(Env, Tvs, Type),
%     {Env_2, PatResults} = checkPatterns(Env_1, Tvs, ClausePatterns, OpenedType),
%     BodyType = hm:get_fn_rt(OpenedType),
%     {Env_3, BodyRes} = checkClauseBody(Env_2, Tvs, ClauseBody, BodyType),
%     {Env_3, Type};
% btc_check(Env, Tvs, Node, Type) ->
%     case type(Node) of
%         Fun when Fun =:= function; Fun =:= fun_expr ->
%             Clauses = case Fun of
%                 function -> function_clauses(Node);
%                 fun_expr -> fun_expr_clauses(Node)
%             end,
%             ClausesCheckRes = lists:map(fun(C) -> btc_check(Env, Tvs, C, Type) end, Clauses),
%             % ?PRINT(ClausesCheckRes),
%             % Result = lists:foldl(
%             %     fun({_Env, Res, _T}, AccRes) ->
%             %         AccRes and Res
%             %     end, true, ClausesCheckRes),
%             {Env, Type};
%         _ ->
%             % io:fwrite("BTC check is not supported, so using synth and subsume ~n"),
%             % ?PRINT(Node),
%             synthAndSubsume(Env, Tvs, Node, Type)
%     end.