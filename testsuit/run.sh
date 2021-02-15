#!/bin/bash

set -euo pipefail

pushd ..
rebar3 escriptize
popd

# run test init case for creating erlang basic module and others
../etc test_init.erl > /dev/null

NoTotal=0
NoFailed=0
NoPassed=0
echo "-------------"
for case in test_cases/*.erl
do
    NoTotal=$((NoTotal+1))
    ExpectedCase=${case//erl/out}
    ExpectedCase=${ExpectedCase//test_cases/expected}
    Result=$(../etc $case)
    Expected=$(cat $ExpectedCase)
    if [ "$Result" == "$Expected" ] ; then
        echo "Test: $case: PASSED"
        NoPassed=$((NoPassed+1))
    else
        #echo $Result
        #echo $Expected
        NoFailed=$(($NoFailed+1))
        echo "Test: $case : FAILED"
        diff <(echo $Result) <(echo $Expected)
    fi
done
echo "-------------"
echo
echo "Summary"
echo "======="
echo "Total : $NoTotal"
echo "Passed: $NoPassed"
echo "Failed: $NoFailed"
echo
echo "test suit exited!"
