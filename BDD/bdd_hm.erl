-module(bdd_hm).
% convert the js code in erlang

% terms
var(Name)        -> {var, Name}.
abs(Name, Body)  -> {abs, Name, Body}.
app(Left, Right) -> {app, Left, Right}.
ann(Term, Type)  -> {ann, Term, Type}.

% types
tVar(Name)           -> {tVar, Name }.
tForall(Name, Body)  -> {tForall, Name, Body}.
tFun(Left, Right)    -> {tFun, Left, Right}.
tApp(Left, Right)    -> {tApp, Left, Right}.
tMeta(Id, Tvs, Mono) -> {tMeta, Id, Tvs, null, Mono}.
tSkol(Id)            -> {tSkol, Id}.
