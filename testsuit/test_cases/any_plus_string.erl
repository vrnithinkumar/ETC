-module (any_plus_string).
-compile(export_all).

f3(X,Y) -> X + Y ;
f3(X,Y) -> X = "", X + Y.

f4(X,Y) -> X + Y;
f4(X,Y) -> "".
