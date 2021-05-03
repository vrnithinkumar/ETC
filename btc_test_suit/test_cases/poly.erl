-module(poly).

% -spec id(T) -> T.
% id(X) -> X.

-spec poly_2(fun((A) -> A))-> {boolean(), integer()}.
poly_2(F) -> {F(true), F(42)}.

% -spec id(T) -> T.
% id(0) -> 0.