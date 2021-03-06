-module(case_union).

-spec union_case(integer() | boolean()) ->  boolean().
union_case(X) ->
    case X of
        true  -> false;
        12 -> true
    end.

-spec union_case_ret(boolean()) ->  integer() | boolean().
union_case_ret(X) ->
    case X of
        true  -> false;
        false -> 42
    end.

% union_case_ret_no_spec(X) ->
%     case X of
%         true  -> false;
%         false -> 42
%     end.

% union_case_no_spec(X) ->
%     case X of
%         true  -> false;
%         12 -> true
%     end.

-spec union_case_ret_with_let(boolean()) -> integer() | boolean().
union_case_ret_with_let(X) ->
    Y = case X of
        true  -> false;
        false -> 42
    end, Y.
    % case X of
    %     true  -> false;
    %     false -> []
    % end.

-spec union_case_ret_with_let_list(boolean()) -> [] | boolean().
union_case_ret_with_let_list(X) ->
    Y = case X of
        true  -> false;
        false -> []
    end, Y.
    % case X of
    %     true  -> false;
    %     false -> []
    % end.