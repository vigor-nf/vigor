This repository contains the Vigor verification toolchain and network functions (NFs).

# Machine prerequisites

Our scripts assume you are using Ubuntu 18.04, with an active Internet connection to download dependencies.
Older Ubuntus, or other Debian-based distros, may work but have not been tested.

As an alternative to installing the dependencies on your own machine, we provide a Docker image: `dslabepfl/vigor`.
However, you must still use Ubuntu 18.04 as a host, since the guest uses the host's kernel and DPDK needs kernel headers to compile.
This image can be generated with the `./Docker-create.sh` script.

To **compile and run** Vigor NFs, you need:

- 16 GB of RAM, 8 GB of which is allocated as 4096x2MB hugepages; see the [DPDK documentation](https://doc.dpdk.org/guides/linux_gsg/sys_reqs.html#linux-gsg-hugepages) to set up hugepages.
- A DPDK-compatible NIC with at least two ports, bound to DPDK using the `dpdk-devbind.py` tool.
- To run `setup.sh no-verify`.

To **verify** NFs using **DPDK models**, you need:

- 16 GB of RAM
- To run `setup.sh` (no arguments)

To **verify** NFs using **hardware models**, you need:

- 256 GB for the bridge, firewall, NAT and policer; 1 TB for the load balancer.
- To run `setup.sh` (no arguments)

To **benchmark** Vigor NFs, you need:

- One 'device under test' machine with the setup described for compiling and running NFs.
- One 'tester' machine, with at least two ports on a DPDK-compatible NIC, each connected to the 'device under test' ports.
- Key-based SSH access to the tester from the device under test. (_This is not strictly required, but will save you from entering your password many times_)
- To change to the `bench/config.sh` file to match the two machines' configuration.


# Compiling, Running, Verifying and Benchmarking Vigor NFs

There are currently five Vigor NFs:

| NF            | Folder      | Description                                                                                                                         |
| ------------- | ----------- | ----------------------------------------------------------------------------------------------------------------------------------- |
| Bridge        | `vigbridge` | Bridge with MAC learning according to [IEEE 802.1Q-2014](https://standards.ieee.org/standard/802_1Q-2014.html) sections 8.7 and 8.8 |
| Firewall      | `vigfw`     | Firewall whose specification we invented                                                                                            |
| Load balancer | `viglb`     | Load balancer inspired by Google's [Maglev](https://ai.google/research/pubs/pub44824)                                               |
| NAT           | `vignat`    | NAT according to [RFC 3022](https://www.ietf.org/rfc/rfc3022.txt)                                                                   |
| Policer       | `vigpol`    | Traffic policer whose specification we invented                                                                                     |

There are additional "baseline" NFs, which can _only be compiled, run and benchmarked_, each in its own folder:

- ??? TODO baselines ???


Pick the NF you want to work with by `cd`-ing to its folder, then use one of the following `make` targets:

| Target(s)                  | Description                                | Expected duration |
| -------------------------- | ------------------------------------------ | ----------------- |
| Default                    | Compile the NF                             | <1min             |
| `run`                      | Run the NF using recommended arguments     | <1min to start    |
| `symbex validate`          | Verify the NF with DPDK models             | 1min to symbex, hours to validate |
| `symbex-withdpdk validate` | Verify the NF with hardware and OS models  | <1h to symbex, hours to validate |
| `symbex-withdsos validate` | Verify the NF with hardware models on DSOS | <1h to symbex, hours to validate |
| `count-loc`                | Count lines of code of the NF              | <1min             |
| `count-dpdk-loc`           | Count lines of code in DPDK                | <1min             |
| `count-dsos-loc`           | Count lines of code in the DSOS            | <1min             |
| `count-spec-loc`           | Count lines of code in the specification   | <1min             |
| `count-libvig-loc`         | Count lines of code of libVig              | <1min             |
| `benchmark-throughput`     | Benchmark the NF's throughput              | ???               |
| `benchmark-latency`        | Benchmark the NF's latency                 | ???               |

To run with your own arguments, compile then run `./build/nf` which will display the command-line arguments you need to pass to the NF.

To verify using a pay-as-you-go specification, add `VIGOR_SPEC=your_spec.py` before a verification command.

For instance:
- To verify the "broadcast" pay-as-you-go property of the  Vigor bridge using DPDK models, run `cd vigbridge` then `VIGOR_SPEC=paygo-broadcast.py make symbex validate`.
- To benchmark the Vigor policer's throughput, run `cd vigpol` then `make benchmark-throughput`


# Using the DSOS

Vigor includes a Domain-Specific Operating System (DSOS) that is simple enough to be symbolically executed, besides trusted boot code.

TODO describe how to make a dsos image with an NF and run it on a commodity server here...


# Writing your own NF

- Run `make new-nf` at the root of the repository, and answer the prompt.


# Dependencies

We depend on, and are grateful for:

- [DPDK](https://www.dpdk.org)
- [KLEE](https://klee.github.io), with our modifications available as [a repository in the same GitHub organization](https://github.com/vignat/klee)
- [KLEE-uClibc](https://github.com/klee/klee-uclibc)
- [OCaml](https://ocaml.org)
- [VeriFast](https://people.cs.kuleuven.be/~bart.jacobs/verifast), with our modifications available as [a repository in the same GitHub organization](https://github.com/vignat/verifast)
- [Z3](https://github.com/Z3Prover/z3/wiki)
