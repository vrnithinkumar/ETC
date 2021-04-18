-module(simple_return).

% -spec foo(integer()) -> boolean().
foo (42) ->
    X = false,
    X and true.
