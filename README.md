ETC
=====


Erlang Type Checker Prototype Based on [Bidirectional Typechecking](https://arxiv.org/abs/1908.05839).

Based on the paper ["Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism"](https://www.cl.cam.ac.uk/~nk480/bidir.pdf) by Jana Dunfield and Neel Krishnaswami.

Based on and extended [Nachi](https://github.com/nachivpn)'s [ETC](https://github.com/nachivpn/mt)

Build And Use
-----
    # Installation
    git clone https://github.com/vrnithinkumar/ETC.git
    rebar3 escriptize

    # Simple usage evaluation example
    ./etc hello.erl

    # Partial evaluation + Type Inference example
    ./etc +pe hello_pe.erl

    # To see the result of code generated by partial evaluation 
    ./etc +pe -P hello_pe.erl #produces hello_pe.P file

    # (only) partial evaluation example
    ./etc +pe +noti -P hello_pe.erl

Run Tests
-----
    cd ./testsuits
    bash run.sh

Using With Rebar3
-----

Add the plugin to your rebar config:

    {plugins, [
        {etc_plug, {git, "https://github.com/vrnithinkumar/ETC.git", {branch, "master"}}}
    ]}.

Then just call your plugin directly in an existing application:

    $ rebar3 etc_plug
    ===> Fetching etc_plug
    ===> Compiling etc_plug
    <Plugin Output>

Update the plugin:

    rebar3 plugins upgrade etc_plug
