-module(env_solver).

-export([solve_envs/2]).

-spec solve_envs(hm:env(), hm:env()) -> hm:env().
solve_envs(Env1, Env2) ->
    Env1.
    % we have to take the two env and solve the type_var_bindings.
