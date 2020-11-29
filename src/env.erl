-module(env).
-export([empty/0,lookup/2,extend/3,extendConstr/3,free/2
        ,is_bound/2,fmapV/2,lookupConstrs/2,default/0
        ,freeInEnv/1,length/1
        ,dumpModuleBindings/2,readModuleBindings/1
        ,lookupRemote/3,extendRecord/4,lookupRecord/2
        ,isPatternInf/1,setPatternInf/1,addGuard/3,checkGuard/2
        ,enableGuardExprEnv/1,disableGuardExprEnv/1
        ,isGuardExprEnabled/1 %,addModuleBindings/2
        ,addExtModuleBindings/2,lookup_ext_binding/2
        ,printExtBindings/1, dumpModuleSpecs/2
        ,readModuleSpecs/1, lookup_spec_binding/2]).

-export_type([env/0]).

%% PRINT Debugging macro%%
-ifndef(PRINT).
-define(PRINT(Var), io:format("DEBUG: ~p:~p - ~p~n~n ~p~n~n", [?MODULE, ?LINE, ??Var, Var])).
-endif.

% Type checker ENvironment
-record(ten, 
    {   bindings        = [],
        ext_bindings    = [],
        specs_bindings  = [],
        constructors    = [],
        recFieldMap     = [],
        guardExpr       = [],
        isPattern       = false,
        isGuardExpr     = false
    }).

-type env() :: ten.

empty() -> #ten{}.

default() -> rt:defaultEnv().

% lookup :: (Var, [Var,Type])  -> Type
lookup({_Func, _ArgCount} = X,Env) -> 
    case proplists:get_value(X,Env#ten.bindings) of 
        undefined -> 
            case look_default_erlang(X,Env) of 
                undefined -> undefined;
                Res       -> Res
            end;
         Res -> Res
    end;
lookup(X,Env) -> proplists:get_value(X,Env#ten.bindings).

lookup_ext_binding(X,Env) -> proplists:get_value(X, Env#ten.ext_bindings).

is_bound(X,Env) -> proplists:is_defined(X,Env#ten.bindings).

extend(X,A,Env) -> Env#ten{bindings = [{X,A} | Env#ten.bindings]}.

addGuard(X,A,Env) -> Env#ten{guardExpr = [{X,A} | Env#ten.guardExpr]}.

checkGuard(X,Env) -> proplists:get_value(X, Env#ten.guardExpr).

enableGuardExprEnv(Env) -> Env#ten{isGuardExpr = true}.

disableGuardExprEnv(Env) -> Env#ten{isGuardExpr = false}.

isGuardExprEnabled(Env) -> Env#ten.isGuardExpr.

extendConstr(X,A,Env) -> Env#ten{constructors = [{X,A} | Env#ten.constructors]}.

free(X,Env) -> Env#ten{bindings = proplists:delete(X,Env#ten.bindings)}.

fmapV(F,Env) -> Env#ten{bindings = lists:map(fun ({Var,Type}) -> {Var,F(Type)} end, Env#ten.bindings)}.

lookupConstrs(X,Env) -> proplists:get_all_values(X,Env#ten.constructors).

%%%%%%%%% Records

extendRecord(R,A,RecFieldMap,Env) -> 
    extendRecFieldMap(R,RecFieldMap,extendConstr(R,A,Env)).

extendRecFieldMap(R,FieldMap,Env) -> 
    Env#ten{recFieldMap = [{R,FieldMap} | Env#ten.recFieldMap]}.

lookupRecord(X,Env) -> 
    case lookupConstrs(X,Env) of
        [A] -> {A,lookupRecFieldMap(X,Env)};
        []  -> undefined
    end.

lookupRecFieldMap(X,Env) -> 
    proplists:get_value(X, Env#ten.recFieldMap).

-spec freeInEnv(hm:env()) -> set:set(hm:tvar()).
freeInEnv (Env) ->
    lists:foldr(
            fun sets:union/2,
            sets:new(),
            lists:map(fun({_,T}) -> hm:free(T)end, Env#ten.bindings)).

length(Env) -> erlang:length(Env#ten.bindings).

dumpModuleBindings(Env,Module) ->
    InterfaceFile = lists:concat([Module,".erltypes"]),
    ModuleBindings = Env#ten.bindings -- ((env:default())#ten.bindings ++ Env#ten.ext_bindings),
    file:write_file(InterfaceFile,erlang:term_to_binary(ModuleBindings)).

readModuleBindings(Module) ->
    InterfaceFile = lists:concat([Module,".erltypes"]),
    {ok, Data} = file:read_file(InterfaceFile),
    erlang:binary_to_term(Data).

dumpModuleSpecs(Spec, Module) ->
    InterfaceFile = lists:concat([Module,".erltypes"]),
    file:write_file(InterfaceFile,erlang:term_to_binary(spec:get_spec_functions(Spec))).

lookup_spec_binding(X,Module) -> proplists:get_value(X, readModuleSpecs(Module)).

readModuleSpecs(Module) ->
    InterfaceFile = lists:concat([Module,".erltypes"]),
    {ok, Data} = file:read_file(InterfaceFile),
    erlang:binary_to_term(Data).

addExtModuleBindings(Env, Module) ->
    Bindings = readModuleBindings(Module),
    Env#ten{ext_bindings = Env#ten.ext_bindings ++ Bindings}.

addModuleBindings(Env, Module) ->
    Bindings = readModuleBindings(Module),
    Env#ten{bindings = Env#ten.bindings ++ Bindings}.

lookupRemote(Module,X,_Env) ->
    dm:type_infer(Module),
    InterfaceFile = lists:concat([Module,".erltypes"]),
    case filelib:is_regular(InterfaceFile)of
        true -> lookup_then_try_with_module(X, Module);
        false -> na
    end.

lookup_then_try_with_module({Func,ArgCount} = X, Module) ->
    case proplists:get_value(X, readModuleBindings(Module)) of
        undefined ->
            NewX = {Module, Func,ArgCount},
            case proplists:get_value(NewX, readModuleBindings(Module)) of
                undefined -> undefined;
                Res -> Res
            end;
        Res -> Res
    end.

look_default_erlang({erlang,Func,ArgCount}, Env) ->
    case lookupRemote(erlang, {Func,ArgCount}, Env) of 
        undefined -> undefined;
        Res       -> Res
    end;
look_default_erlang(X, Env) ->
    case lookupRemote(erlang, X, Env) of 
        undefined -> undefined;
        Res       -> Res
    end.

printExtBindings(Env) ->
    Ext = Env#ten.ext_bindings,
    ?PRINT(Ext).
%%%%%%%%%%%%%%%%%%%
isPatternInf(Env) -> 
    Env#ten.isPattern.

setPatternInf(Env) ->
    Env#ten{isPattern = true}.
