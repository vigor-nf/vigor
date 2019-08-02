This repository contains the Vigor verification toolchain and network functions (NFs).

# Machine prerequisites

Our scripts assume you are using Ubuntu 18.04, with an active Internet connection to download dependencies.
Older Ubuntus, or other Debian-based distros, may work but have not been tested.

To **compile and run** Vigor NFs, you need:

- At least 16 GB of RAM, 8 GB of which is allocated as 4096x2MB hugepages; see the [DPDK documentation](https://doc.dpdk.org/guides/linux_gsg/sys_reqs.html#linux-gsg-hugepages) to set up hugepages.
- A DPDK-compatible NIC with at least two ports, bound to DPDK using the `dpdk-devbind.py` tool.
- To run `setup.sh no-verify`.

To **verify** NFs using **DPDK models**, you need:

- ??? TODO: Measure max RAM usage of verifying NFs with dpdk stubs, pad a healthy margin ???
- To run `setup.sh` (no arguments)

To **verify** NFs using **hardware models**, you need:

- At least 128 GB of RAM
- As many CPU cores as you can find, since the Vigor Validator is embarassingly parallelizable
- To run `setup.sh` (no arguments)

To **benchmark** Vigor NFs, you need:

- One 'device under test' machine with the setup described for compiling and running NFs.
- One 'tester' machine, with at least two ports on a DPDK-compatible NIC, each connected to the 'device under test' ports.
- Key-based SSH access to the tester from the device under test. (_This is not strictly required, but will save you from entering your password many times_)
- To change to the `bench/config.sh` file to match the two machines' configuration.


# Compiling, Running, Verifying and Benchmarking Vigor NFs

There are currently five Vigor NFs, each in its own folder:

- `vigbridge`, a bridge with MAC learning according to [IEEE 802.1Q-2014](https://standards.ieee.org/standard/802_1Q-2014.html) sections 8.7 and 8.8
- `vigfw`, a firewall whose specification we invented
- `viglb`, a load balancer inspired by Google's [Maglev](https://ai.google/research/pubs/pub44824)
- `vignat`, a NAT according to RFC 3022
- `vigpolicer`, a traffic policer whose specification we invented

There are additional "baseline" NFs, which can _only be compiled, run and benchmarked_, each in its own folder:

- ??? TODO baselines ???


Pick the NF you want to work with by `cd`-ing to its folder.

To **compile**, run `make`.

To **run**, run `make run` to use recommended arguments, or compile then run `./build/nf` which will display the command-line arguments you need to pass to the NF.

To **verify with DPDK models**, run `make symbex validate`.

To **verify with hardware models**, run `make symbex-fullstack validate`.

To **verify using a pay-as-you-go specification**, add `VIGOR_SPEC=your_spec.py` before the verify command.

To **count the lines of code of the NF**, run `make count-loc`.

To **count the lines of code of the NF including DPDK**, run  `make count-fullstack-loc`.

To **count the lines of code of the spec**, run `make count-spec-loc`.

To **count the lines of code of libVig**, run `make count-lib-loc`.

To **count the lines of code of the DSOS**, run `make count-os-loc`

To **benchmark**, run `make benchmark-throughput` or `make benchmark-latency`.


For instance, to verify the "broadcast" pay-as-you-go property of VigBridge using DPDK models,
run `cd vigbridge` then `VIGOR_SPEC=paygo-broadcast.py make symbex validate`.


# Dependencies

We depend on, and are grateful for:

- [DPDK](https://www.dpdk.org)
- [KLEE](https://klee.github.io), with our modifications available as [a repository in the same GitHub organization](https://github.com/vignat/klee)
- [KLEE-uClibc](https://github.com/klee/klee-uclibc)
- [OCaml](https://ocaml.org)
- [VeriFast](https://people.cs.kuleuven.be/~bart.jacobs/verifast), with our modifications available as [a repository in the same GitHub organization](https://github.com/vignat/verifast)
- [Z3](https://github.com/Z3Prover/z3/wiki)
