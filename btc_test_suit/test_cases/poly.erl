-module(poly).
-export([poly_2/1, poly_fail/3]).
% -spec id(T) -> T.
% id(X) -> X.

-spec poly_2(fun((A) -> A))-> {boolean(), integer()}.
poly_2(F) -> {F(true), F(42)}.

-spec poly_fail(fun((A) -> A), boolean(), integer())
    -> {boolean(), integer()}.
poly_fail(F, B, I) -> {F(I), F(B)}.

% -spec id(T) -> T.
% id(0) -> 0.