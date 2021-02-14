-module(tc).

-import(erl_syntax,[
    function_clauses/1,
    fun_expr_clauses/1,
    clause_patterns/1,
    clause_body/1,
    clause_guard/1,
    type/1
]).

-export([type_check/2]).

%% PRINT Debugging macro%%
-ifndef(PRINT).
-define(PRINT(Var), io:format("DEBUG: ~p:~p - ~p~n~n ~p~n~n", [?MODULE, ?LINE, ??Var, Var])).
-endif.

type_check(Env, F) ->
    FunQName = util:getFnQName(F),
    Specs = env:getSpecs(Env),
    case spec:hasUserSpecifiedSpec(Specs, FunQName) of
        true ->
            SpecFT = spec:getFirstSpecType(Specs, FunQName),
            do_infer_type_check(Env, F, SpecFT);
        false -> false
    end.

do_infer_type_check(Env, F, SpecFT) ->
    FunQName = util:getFnQName(F),
    ResCheck = check(Env, F, SpecFT),
    % ?PRINT(ResCheck),
    % ?PRINT(FunQName),
    % ?PRINT(SpecFT),
    % ?PRINT(F),
    true.

-spec check(hm:env(), erl_syntax:syntaxTree(), hm:type()) ->
    {hm:env(), boolean(), hm:type()}.
check(Env, {integer,L,_}, Type) ->
    Inferred = hm:bt(integer,L),
    IsSame = hm:is_same(Inferred, Type),
    {Env, IsSame, Inferred};
check(Env, {string,L,_}, Type) ->
    Inferred = hm:tcon("List", [hm:bt(char,L)],L),
    IsSame = hm:is_same(Inferred, Type),
    {Env, IsSame, Inferred};
check(_,{char,L,_}, Type) ->
    Inferred = hm:bt(char,L),
    IsSame = hm:is_same(Inferred, Type),
    {IsSame, Inferred};
check(Env, {float,L,_}, Type) ->
    Inferred = hm:bt(float, L),
    IsSame = hm:is_same(Inferred, Type),
    {Env, IsSame, Inferred};
check(Env, {atom,L,X}, Type) ->
    Inferred = case X of
        B when is_boolean(B) -> hm:bt(boolean, L);
        _                    -> hm:bt(atom, L)
        end,
    IsSame = hm:is_same(Inferred, Type),
    {Env, IsSame, Inferred};
check(Env, {var, L, '_'}, Type) ->
    {Env, true, Type};
check(Env, {var, L, X}, Type) ->
    {VarT, _Ps} = etc:lookup(X, Env, L),
    IsSame = hm:is_same(VarT, Type),
    {Env, IsSame, VarT};
check(Env,{match,_, LNode, RNode}, Type) ->
    ?PRINT(LNode),
    % {Env_, Cons1, Ps} = checkExpr(Env,LNode),
    % {LType, Cons2, PsL} = infer(Env_,LNode),
    % {RType, Cons3, PsR} = infer(Env,RNode),
    % { RType
    % , Cons1 ++ Cons2 ++ Cons3 ++ unify(LType,RType)
    % , Ps ++ PsL ++ PsR};
    {Env, true, Type};
check(Env,{ op, L, Op, E1, E2}, Type) ->
    {OpType, _Ps} = etc:lookup(Op, Env, L),
    Arg1Type = hd(hm:get_fn_args(OpType)),
    Arg2Type = lists:last(hm:get_fn_args(OpType)),
    RetType = hm:get_fn_rt(OpType),
    {Res1, _T1} = check(Env, E1, Arg1Type),
    {Res2, _T2} = check(Env, E2, Arg2Type),
    IsSame = hm:is_same(RetType, Type),
    {Env, Res1 and IsSame and Res2, RetType};
check(Env, {clause,L,_,_,_}=Node, Type) ->
    ClausePatterns = clause_patterns(Node),
    ClauseBody = clause_body(Node),
    PatRes = checkPatterns(Env, ClausePatterns, Type),
    ClauseGaurds = clause_guard(Node),
    BodyType = hm:get_fn_rt(Type),
    BodyRes = checkClauseBody(Env, ClauseBody, BodyType),
    {Env, false, Type};
check(Env, Node, Type) ->
    case type(Node) of
        Fun when Fun =:= function; Fun =:= fun_expr ->
            Clauses = case Fun of
                function -> function_clauses(Node);
                fun_expr -> fun_expr_clauses(Node)
            end,
            ClausesCheckRes = lists:map(fun(C) -> check(Env, C, Type) end, Clauses),
            {Env, true, Type};
        X -> erlang:error({type_error," Cannot check the type of " 
            ++ util:to_string(Node) ++ " with node type "++ util:to_string(X)})
    end;
check(_,Expr, Type) ->
    io:format("Not supported Type-Check: ~p:~p ~n", [Expr, Type]).

% check if the arg patterns are matching.
-spec checkPatterns(hm:env(),[erl_syntax:syntaxTree()], hm:types()) -> 
    {[boolean()], [hm:types()]}.
checkPatterns(Env, ClausePatterns, Type) ->
    ArgTypes = hm:get_fn_args(Type),
    ArgAndTypes = lists:zip(ClausePatterns, ArgTypes),
    lists:foldl(
        fun({ArgPattern, ArgType},{AccRs, AccTs}) ->
            {Res, CType} = checkArgType(Env, ArgPattern, ArgType),
            {AccRs ++ [Res], AccTs ++ [CType]}
        end, {[],[]}, ArgAndTypes).

% check if the arg expr has given arg type.
-spec checkArgType(hm:env(), erl_syntax:syntaxTree(), hm:types()) -> 
    {boolean(), hm:types()}.
checkArgType(Env, ArgPattern, ArgType) ->
    check(Env, ArgPattern, ArgType).

% check if the arg patters are matching.
% given a body of a clause, returns its type
-spec checkClauseBody(hm:env(), erl_syntax:syntaxTree(), hm:types()) -> 
    {boolean(), hm:types()}.
checkClauseBody(Env, Body, Type) ->
    {Env_, CsBody, PsBody} = lists:foldl(
        fun(Expr, {Ei,Csi,Psi}) -> 
            {Ei_,Csi_,Psi_} = check(Ei, Expr, Type),
            {Ei_, Csi ++ Csi_, Psi ++ Psi_}
        end, {Env,[],[]}, lists:droplast(Body)),
    check(Env, lists:last(Body), Type).