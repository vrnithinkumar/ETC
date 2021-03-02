-module(bdd_hm).

-export([tests/0]).

% convert the js code in erlang

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

tests() ->
    IDType = tForall("t", tFun(tVar("t"), tVar("t"))),
    VAR_ = var("X"),
    ID_ABS = abs("X", VAR_),
    APP_ = app(ID_ABS, VAR_),
    ANN_ = ann(ID_ABS, IDType),
    lists:map(fun(Term) -> showTerm(Term) end, [VAR_, ID_ABS, APP_, ANN_])
    .