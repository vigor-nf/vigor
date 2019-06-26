# Hardware testbench

This folder contains the scripts necessary to benchmark Vigor NFs, Linux's NAT (NetFilter),
and any other DPDK-based software obeying VigNAT's public parameters "API", such as the provided nop and unverified nat applications.

## Hardware setup

2 machines are required, each with an interface connected to the outside world and an associated hostname.  
All machines must be able to talk to each other by going through the outside world.  
As Vigor NFs are DPDK-based apps, the machines must have DPDK-compatible NICs.

The 1st machine is the tester, the 2nd is the middlebox.
There must be 2 connections between tester and middlebox.

## Software setup

Create an SSH key on the NF and add its public key to the tester, as the scripts use SSH extensively.

Edit the `config.sh` file to set the machines' names and addresses.

## Running benchmarks

Benchmarks are run from the NAT machine.

The single entry point to all benchmarks is `bench.sh`. It takes two arguments.  
The first argument is either `netfilter` or the path to a VigNAT-like app.  
The second argument is the scenario, one of:  
- `throughput` to measure maximal throughput with <0.1% loss;
- `latency` to measure latency under load;

The script outputs a `.results` file with the results. When testing a VigNAT-like app, a `.log` file will also be generated containing the standard output of the app.
