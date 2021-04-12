# TODO

## BDTC
- [ ] Add if else
  - [X] Simple if case is support
  - [ ] Union type check / inference
- [ ] Simple case structure
- [ ] Let statements
- [ ] Union type support

## ETC
- [X] Integrate the BDTC to ETC
  - [X] Simple erlang function
  - [-] Full support
    - [X] (_,{integer,L,_})
    - [X] (_, {string,L,_})
    - [X] (_,{char,L,_}) ->
    - [X] (_,{float,L,_}) ->
    - [ ] (Env,{clause,L,_,_,_}=Node) ->
    - [X] (_,{var,L,'_'}) ->
    - [ ] (Env,{var, L, X}) ->
    - [ ] (Env,{call,L,{atom,_,is_function},[F,{integer,_,Arity}]}) ->
    - [ ] (Env,{call,L,{atom,_,element},[{integer,_,N},{tuple,_,Es}]}) ->
    - [ ] (Env,{call,L,F,Args}) ->
    - [ ] (Env,{op,L,Op,E1,E2}) ->
    - [ ] (Env,{atom,L,X}) ->
    - [ ] (Env,{'fun',L,{function,X,ArgLen}}) ->
    - [ ] (_,{nil,L}) ->
    - [ ] (Env,{cons,L,H,T}) ->
    - [ ] (Env,{tuple,L,Es}) ->
    - [ ] (Env,{'if',_,Clauses}) ->
    - [ ] (Env,{'case',_,Expr,Clauses}) ->
    - [ ] (Env,{'receive',_,Clauses}) ->
    - [ ] (Env,{match,_,LNode,RNode}) ->
    - [ ] (Env,{lc,L,Expr,Defs}) ->
    - [ ] (Env,{block,_,Exprs}) ->
    % Create a record value
    - [ ] (Env,{record,L,Rec,FieldValues}) ->
    % Update a record
    - [ ] (Env,{record,L,Expr,Rec,FieldValues}) ->
    % Access a record
    - [ ] (Env,{record_field,L,Expr,Rec,{atom,_,Field}}) ->
    - [ ] (Env,{'try',L,TryExprs,[],CatchClauses,AfterExprs}) ->
    - [ ] (Env,Node) -
- [ ] Run the benchmark tests from ETC-HM
- [ ] Run on antidote db

## Type Rules
- [ ] Define Type rules for core erlang
- [ ] Very basic using polymorphic bd type checking rules
