-module(poly).
-spec id(T) -> T.
id(X) -> X.

-spec foo(fun((A) -> A))-> {atom(), boolean()}.
foo(F) -> {F(helo), F(false)}.
