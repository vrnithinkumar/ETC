-module(poly_spec_eg).

% -spec map(fun((A) -> B),[A]) -> [B].
map(F,[])  -> []; 
map(F,[X|Xs]) -> [F(X)|map(F,Xs)].

e1() -> map(fun(X)->not(X) end,[1,2]). %this expression will fail 
e2() -> map(fun(X)->not(X) end,[true,false]).