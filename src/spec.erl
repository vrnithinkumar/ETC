-module(spec).
-import(erl_syntax,[
    function_clauses/1,
    fun_expr_clauses/1,
    clause_patterns/1,
    clause_body/1,
    clause_guard/1,
    type/1
]).

%% PRINT Debugging macro%%
-ifndef(PRINT).
-define(PRINT(Var), io:format("DEBUG: ~p:~p - ~p~n~n ~p~n~n", [?MODULE, ?LINE, ??Var, Var])).
-endif.

-export([parse_transform/2]).
-export([empty/0, lookup/2, extend/3, add_functions/2,
         get_spec_functions/1, hasUserSpecifiedSpec/2,
         getFirstSpecType/2]).
-export_type([spec/0]).

% Type checker ENvironment
-record(specenv, 
    {   functions = [],
        exp_types = []
    }).

-type spec() :: specenv.
empty() -> #specenv{}.

parse_transform(Forms,_Opt) ->
    Mods_ = pp:getImprtdMods(Forms),
    pp:eraseAnn(Forms).

extend(X,A,Spec) -> Spec#specenv{functions = [{X,A} | Spec#specenv.functions]}.

add_functions(Fs,Spec) -> Spec#specenv{functions = Fs}.

get_spec_functions(Spec) -> Spec#specenv.functions.

lookup(X, Spec) -> proplists:get_value(X, get_spec_functions(Spec)).

hasUserSpecifiedSpec(Spec, X) ->
    case lookup(X, Spec) of
        undefined -> false;
        _         -> true
    end.

getFirstSpecType(Spec, X) ->
    SpecTs = lookup(X, Spec),
    % hd(SpecTs).
    % Have to fixe multi spec type for same func
    SpecTs.
