-module(union_return).

-spec foo(integer(), boolean()) -> integer() | boolean().
foo (45, false) ->
    123;
foo (32, true) ->
    X = false,
    X and true.
