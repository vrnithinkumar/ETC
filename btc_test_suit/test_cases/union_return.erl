-module(union_return).

% -spec foo(integer(), boolean()) -> integer() | boolean().
% foo (45, false) ->
%     123;
% foo (32, true) ->
%     X = false,
%     X and true.

-spec union_case(integer() | boolean()) ->  boolean().
union_case(X) ->
    case X of
        true  -> false;
        12 -> true
    end,
    X.