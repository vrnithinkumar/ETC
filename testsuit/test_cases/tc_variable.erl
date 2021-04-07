-module(tc_variable).
-compile(export_all).

-spec f1(boolean()) -> integer().
f1(X) -> 42.

-spec f2(integer()) -> integer().
f2(X) -> X + 42.

% -spec id_bool(boolean()) -> boolean().
% id_bool(X) -> X.
