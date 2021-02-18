-module(basic_bd_tc).
-compile(export_all).

-spec f1() -> integer().
f1() -> 42.

-spec f2() -> float().
f2() -> 3.14 .

-spec f3() -> string().
f3() -> "Hello".

-spec f4() -> char().
f4() -> $N.

-spec f5() -> boolean().
f5() -> true.

-spec f6() -> boolean().
f6() -> false.

-spec f7(integer()) -> integer().
f7(13) -> 123.

-spec f8(boolean()) -> integer().
f8(false) -> 123.
