-module(dm).

%% PRINT Debugging macro%%
-ifndef(PRINT).
-define(PRINT(Var), io:format("DEBUG: ~p:~p - ~p~n~n ~p~n~n", [?MODULE, ?LINE, ??Var, Var])).
-endif.

-export([type_check_mods/2, type_infer/1]).

type_check_mods(Mods, File) ->
    FilteredMods = lists:filter(fun(M) -> not checkedModule(M) end,Mods),
    ModPaths = get_module_paths(FilteredMods, File),
    check_modules_path(ModPaths).

get_module_paths(Modules, Path) ->
    Base = string:join(lists:droplast(string:tokens(Path, "/")), "/"),
    lists:map(fun(M) -> 
        MP = Base ++ "/" ++ atom_to_list(M) ++ ".erl",
        case filelib:is_regular(MP) of
            true  -> MP;
            false -> registerAsLib(M), getLibModulePath(M)
        end
    end, Modules).

check_modules_path(Modules)->
    lists:map(fun(M) ->
        io:fwrite("Running etc for dependent module ~p ~n~n",[M]),
        main_spec([M])
     end, Modules).

spawn_and_wait(M,F,Arg) ->
    process_flag(trap_exit, true),
    {_Pid, MonitorRef} = spawn_monitor(M, F, [[Arg]]),
    ?PRINT(_Pid),
    receive
        {_Tag, MonitorRef, _Type, _Object, _Info} -> ok
    after 9000 ->
        timeout
    end.

spawn_and_trap(M,F,Arg) ->
    Pid = spawn_link(M, F, [[Arg]]),
    ?PRINT(Pid),
    receive
	{'EXIT', Pid, Reason} -> Reason
    end.

main_spec(Args0) ->
    Args = ["+{parse_transform, tidy}"] ++ 
    case lists:member("+noti",Args0) of
        true -> [];
        false -> ["+{parse_transform, etc}"]
    end ++ 
    case lists:member("+pe",Args0) of
        true -> ["+{parse_transform, pe}"];
        false -> []
    end ++ Args0,
    erl_compile2:compile(Args).

save_env(File, Env) ->
    ErlTypeFile = re:replace(File, "\\.erl", "\\.erltypes", [{return,list}]),
    save_to_file(ErlTypeFile, Env).

save_to_file(FileName, Data) ->
    BD = erlang:term_to_binary(Data),
    file:write_file(FileName, io_lib:fwrite("~p.", [BD])).

open_from_file(FileName) ->
    {ok, [Data]} = file:consult(FileName),
    erlang:binary_to_term(Data).

search_stdlib(ModueName) ->
    code:lib_dir(stdlib, ModueName).

type_infer(Module)->
    case ets:lookup(compile_config, main_file) of 
        [] -> io:fwrite("No base file found ~n");
        [{main_file, File}] -> lookupModule(Module, File)
    end.

lookupModule(Module, File) ->
    case checkedModule(Module) of 
        true -> na;
        false ->
            case getLibModulePath(Module) of 
                no_lib_module -> type_check_mods([Module], File);
                Path -> registerAsLib(Module), check_modules_path([Path])
            end
    end.

getLibModulePath(Module) ->
    LibDir = code:lib_dir(),
    ModString = atom_to_list(Module),
    WC = LibDir ++ "/*/src/" ++ ModString ++ ".erl",
    case filelib:wildcard(WC) of
        [] -> no_lib_module;
        [Path | _] -> Path
    end.

checkedModule(Module) ->
    isAlreadyChecking(Module) or moduleDumpExists(Module).

isAlreadyChecking(Module) -> 
    case ets:lookup(compile_config, Module) of 
        [] ->  false;
        _  -> true
    end.

registerAsLib(Module) -> 
    ets:insert(compile_config, {Module, stdlib}).

moduleDumpExists(Module) ->
    MIF = atom_to_list(Module) ++ ".erltypes",
    filelib:is_regular(MIF).