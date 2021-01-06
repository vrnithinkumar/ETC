-module(etc_plug).

-export([init/1, do/1, format_error/1]).

-define(PROVIDER, etc_plug).
-define(DEPS, [app_discovery]).

%% PRINT Debugging macro%%
-ifndef(PRINT).
-define(PRINT(Var), io:format("DEBUG: ~p:~p - ~p~n~n ~p~n~n", [?MODULE, ?LINE, ??Var, Var])).
-endif.

%% ===================================================================
%% Public API
%% ===================================================================
-spec init(rebar_state:t()) -> {ok, rebar_state:t()}.
init(State) ->
    Provider = providers:create([
            {name, ?PROVIDER},            % The 'user friendly' name of the task
            {module, ?MODULE},            % The module implementation of the task
            {bare, true},                 % The task can be run by the user, always true
            {deps, ?DEPS},                % The list of dependencies
            {example, "rebar3 etc_plug"}, % How to use the plugin
            {opts, []},                   % list of options understood by the plugin
            {short_desc, "A rebar plugin for etc"},
            {desc, "A rebar plugin erlang type checker"}
    ]),
    {ok, rebar_state:add_provider(State, Provider)}.


-spec do(rebar_state:t()) -> {ok, rebar_state:t()} | {error, string()}.
do(State) ->
    code:add_pathsa(rebar_state:code_paths(State, all_deps)),
    CheckedApps = lists:map(fun etc_check_app/1, rebar_state:project_apps(State)),
    HasNok = lists:member(nok, CheckedApps),
    if
        HasNok -> {error, {?MODULE, undefined}};
        true -> {ok, State}
    end.


-spec format_error(any()) -> string().
format_error(_) ->
    "ETC found errors.".

-spec etc_check_app(rebar_app_info:t()) -> ok | nok.
etc_check_app(App) ->
    Files = files_to_check(App),
    io:fwrite("Files to check: ~n ~p ~n",[Files]), 
    lists:map(fun (F) -> etc:main([F]) end, Files),
    ok.

%% get files to run the type checker.
-spec files_to_check(rebar_app_info:t()) -> [file:name()].
files_to_check(App) ->

    Opts = rebar_app_info:opts(App),
    Deps = rebar_app_info:deps(App),
    ?PRINT(Deps),
    OutDir = rebar_app_info:out_dir(App),
    ?PRINT(OutDir),

    ETCOpts = rebar_app_info:get(App, etc_opts, []),
    Include = proplists:get_value(include, ETCOpts, undefined),
    Exclude = proplists:get_value(exclude, ETCOpts, []),
    Cwd = rebar_app_info:dir(App),

    Patterns = case Include of
        undefined ->
            {SrcDirs, ExtraDirs} = resolve_src_dirs(Opts),
            lists:map(fun(File) ->
                filename:join(filename:absname(File, Cwd), "*.erl")
            end, SrcDirs ++ ExtraDirs);
        _ -> Include
    end,
    Files = lists:flatmap(fun (Pattern) ->
            filelib:wildcard(filename:absname(Pattern, Cwd))
        end, Patterns),
    ExpandedFiles = lists:flatmap(fun (Dir) ->
            case filelib:is_dir(Dir) of
                true ->
                    filelib:wildcard(filename:join(Dir, "*.{erl,beam}"));
                false ->
                    [Dir]
            end
        end, Files),
    ExpandedExclude = lists:flatmap(fun (Pattern) ->
                filelib:wildcard(filename:absname(Pattern, Cwd))
            end, Exclude),
    lists:filter(
        fun (File) ->
            not lists:member(File, ExpandedExclude)
        end, ExpandedFiles).

-spec resolve_src_dirs(dict:dict()) -> {[file:name()], [file:name()]}.
resolve_src_dirs(Opts) ->
    SrcDirs = rebar_dir:src_dirs(Opts, ["src"]),
    ExtraDirs = rebar_dir:extra_src_dirs(Opts, []),
    normalize_src_dirs(SrcDirs, ExtraDirs).

%% remove duplicates and make sure no directories that exist
%% in src_dirs also exist in extra_src_dirs
-spec normalize_src_dirs([file:name()], [file:name()]) -> {[file:name()], [file:name()]}.
normalize_src_dirs(SrcDirs, ExtraDirs) ->
    S = lists:usort(SrcDirs),
    E = lists:subtract(lists:usort(ExtraDirs), S),
    {S, E}.