-module(poly).

-spec id(T) -> T.
id(X) -> X.

-spec poly_2(fun((A) -> A))-> {char(), boolean()}.
poly_2(F) -> {F($N  ), F(false)}.
