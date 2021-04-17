-module(ping_pong).
-compile(export_all).

-type protocol() :: {ping, pid()} | {pong, pid()}.

pingClient(ServerPid) ->
    ServerPid ! {ping, self()},
    receive
        {pong,_} ->
            "Done"
    end.

pongServer() ->
    receive
        {ping, Ping_PID} ->
            Ping_PID ! {pong, self()},
            pongServer()
    end.

start()->
    ServerPid = spawn(fun pongServer/0),
    spawn(fun () -> pingClient(ServerPid) end),
    ok.