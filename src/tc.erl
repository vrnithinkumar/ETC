-module(tc).

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
            ?PRINT(FunQName),
            ?PRINT(SpecFT),
            true;
        false -> false
    end.