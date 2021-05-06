-module(poly_spec_eg).

-spec map(fun((A) -> B),[A]) -> [B].
map(F,[]) -> []; 
map(F,[X|Xs]) -> [F(X)|map(F,Xs)].

e1() -> map(fun(X)-> (X and X) end,[1,2]). %this expression will fail 
% e2() -> map(fun(X)-> (X or X) end,[true,false]).