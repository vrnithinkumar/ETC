-module(poly_spec).

% -spec id(T1, any()) -> T1.
% % id(X, Y) -> X.
% id(X, Y) -> Y.

% map(F,[]) -> []; 
%   map(F,[X|Xs]) -> [F(X)|map(F,Xs)].

% foo([X|Xs]) -> foo(Xs).
% -spec map(Function, [T1]) -> T2 when
%       Function :: fun((T1) -> T2).
% map(F, [X|Xs]) -> F(X).

% -spec foo(boolean(), integer()) -> {boolean(), integer()}.
% foo(X, Y) -> {X, Y}.
% foo(X, Y) -> {Y, X}. %% Fails

-spec fooPoly(T1, T2) -> {T1, T2}.
fooPoly(X, Y) -> {X, Y}.
% fooPoly(X, Y) -> {Y, X}. %% Fails

% e1() -> map(fun(X)-> not(X) end,[1,2]). %this expression will fail 
% e2() -> map(fun(X)->not(X) end,[true,false]).

%SKOL
% -spec foo(integer()) -> integer().
% foo(X) -> X.

-spec id(T) -> T.
id(X) -> X.
% foo(X, Y) -> {Y, X}. %% Fails

-spec list_foo([T1]) -> T1.
list_foo([X|Xs]) -> id(X).
