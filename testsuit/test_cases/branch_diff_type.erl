-module(branch_diff_type).
-compile(export_all).

ping() -> 1.0.

pong() -> pong.

% unused case can have branches of different types
foo(X) ->
    case X of
        ping -> ping();
        pong -> pong()
    end,
    trash.