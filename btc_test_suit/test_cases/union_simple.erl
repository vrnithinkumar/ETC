-module(union_simple).

% -spec foo(integer()| boolean()) -> integer().
foo(X) -> 
    case X of 
        false -> 13;
        12 -> 42
    end.