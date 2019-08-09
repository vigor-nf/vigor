# NOTE: Dear SOSP AE reviewer, while all the code of the artifact is in this repo, there are a few things we haven't written up properly yet, and this repo hasn't been thoroughly tested; but the artifact is available, and we fully intend to have all descriptions/scripts working for the 'results replicated' deadline


This repository contains the Vigor verification toolchain and network functions (NFs).

# Machine prerequisites

Our scripts assume you are using Ubuntu 18.04, with an active Internet connection to download dependencies.
Older Ubuntus, or other Debian-based distros, may work but have not been tested.

As an alternative to installing the dependencies on your own machine, we provide a Docker image: `dslabepfl/vigor`.
However, you must still use Ubuntu 18.04 as a host, since the guest uses the host's kernel and DPDK needs kernel headers to compile.
This image can be generated with the `./Docker-create.sh` script.

_Please note that running the setup.sh script can take an hour, since it downloads and compiles many dependencies._

To **compile and run** Vigor NFs, you need:

- 16 GB of RAM, 8 GB of which is allocated as 4096x2MB hugepages; see the [DPDK documentation](https://doc.dpdk.org/guides/linux_gsg/sys_reqs.html#linux-gsg-hugepages) to set up hugepages.
- A DPDK-compatible NIC with at least two ports, bound to DPDK using the `dpdk-devbind.py` tool.
- To run `setup.sh no-verify`.

To **verify** NFs using **DPDK models**, you need:

- 16 GB of RAM
- To run `setup.sh` (no arguments)

To **verify** NFs using **hardware models**, you need:

- 128 GB of RAM
- To run `setup.sh` (no arguments)

To **benchmark** Vigor NFs, you need:

- One 'device under test' machine with the setup described for compiling and running NFs, and a kernel setup for performance (see the `Linux setup for performance` section below)
- One 'tester' machine, with at least two ports on a DPDK-compatible NIC, each connected to the 'device under test' ports
- Key-based SSH access to the tester from the device under test (_This is not strictly required, but will save you from entering your password many times_)
- To change the `bench/config.sh` file to match the two machines' configuration


# Vigor NFs

There are currently five Vigor NFs:

| NF            | Folder      | Description                                                                                                                         |
| ------------- | ----------- | ----------------------------------------------------------------------------------------------------------------------------------- |
| Bridge        | `vigbridge` | Bridge with MAC learning according to [IEEE 802.1Q-2014](https://standards.ieee.org/standard/802_1Q-2014.html) sections 8.7 and 8.8 |
| Firewall      | `vigfw`     | Firewall whose specification we invented                                                                                            |
| Load balancer | `viglb`     | Load balancer inspired by Google's [Maglev](https://ai.google/research/pubs/pub44824)                                               |
| NAT           | `vignat`    | NAT according to [RFC 3022](https://www.ietf.org/rfc/rfc3022.txt)                                                                   |
| Policer       | `vigpol`    | Traffic policer whose specification we invented                                                                                     |

There are additional "baseline" NFs, which can _only be compiled, run and benchmarked_, each in its own folder:

| NF                  | Folder              | Description                            |
| ------------------- | ------------------- | -------------------------------------- |
| Click bridge        | `click-bridge`      | Click-based MAC learning bridge        |
| Click firewall      | `click-fw`          | Click-based firewall                   |
| Click load balancer | `click-lb`          | Click-based load balancer (not Maglev) |
| Click NAT           | `click-nat`         | Click-based NAT                        |
| Click no-op         | `click-nop`         | Click-based no-op (rewrites headers)   |
| Moonpol             | `moonpol`           | Libmoon-based traffic policer          |
| Unverified NAT      | `unverified-nat`    | DPDK-based NAT                         |
| Unverified no-op    | `unverified-nop`    | DPDK-based no-op (rewrites headers)    |
| Unverified router   | `unverified-router` | DPDK-based router                      |

The Click- and Libmoon-based NFs use batching if the `VIGOR_USE_BATCH` environment variable is set to `true`.


Pick the NF you want to work with by `cd`-ing to its folder, then use one of the following `make` targets:

| Target(s)                  | Description                                | Expected duration                  |
| -------------------------- | ------------------------------------------ | ---------------------------------- |
| Default                    | Compile the NF                             | <1min                              |
| `run`                      | Run the NF using recommended arguments     | <1min to start                     |
| `symbex validate`          | Verify the NF with DPDK models             | <1min to symbex, hours to validate |
| `symbex-withdpdk validate` | Verify the NF with hardware and OS models  | <1h to symbex, hours to validate   |
| `symbex-withdsos validate` | Verify the NF with hardware models on DSOS | <1h to symbex, hours to validate   |
| `count-loc`                | Count LoC in the NF                        | <1min                              |
| `count-spec-loc`           | Count LoC in the specification             | <1min                              |
| `count-dsos-loc`           | Count LoC in the DSOS                      | <1min                              |
| `count-libvig-loc`         | Count LoC in libVig                        | <1min                              |
| `count-libvig-ds-loc`      | Count LoC in libVig data structures        | <1min                              |
| `count-dpdk-loc`           | Count LoC in DPDK (not drivers)            | <1min                              |
| `count-ixgbe-loc`          | Count LoC in the ixgbe driver              | <1min                              |
| `count-uclibc-loc`         | Count LoC in KLEE-uClibc                   | <1min                              |
| `benchmark-throughput`     | Benchmark the NF's throughput              | <30min                             |
| `benchmark-latency`        | Benchmark the NF's latency                 | <10min                             |

To run with your own arguments, compile then run `sudo ./build/app/nf -- -?` which will display the command-line arguments you need to pass to the NF.

To verify using a pay-as-you-go specification, add `VIGOR_SPEC=paygo-your_spec.py` before a verification command; the spec name must begin with `paygo-` and end with `.py`.

For instance:
- To verify the "broadcast" pay-as-you-go property of the  Vigor bridge using DPDK models, run `cd vigbridge` then `VIGOR_SPEC=paygo-broadcast.py make symbex validate`.
- To benchmark the Vigor policer's throughput, run `cd vigpol` then `make benchmark-throughput`


# Using the DSOS

Vigor includes a Domain-Specific Operating System (DSOS) that is simple enough to be symbolically executed, besides trusted boot code.

TODO describe how to make a dsos image with an NF and run it on a commodity server here...


# Making your own NF

- Run `make new-nf` at the root of the repository, and answer the prompt.


# Linux setup for performance

To maximize and stabilize performance, we recommend the following Linux kernel switches in `/etc/default/grub`'s `GRUB_CMDLINE_LINUX_DEFAULT`:

These settings were obtained from experience and various online guides, such as Red Hat's low-latency tuning guides. They are designed for Intel-based machines, you may have to tweak some of them if you use AMD CPUs.

Please do not leave these settings enabled if you aren't benchmarking, as they will effectively cause your machine to always consume a lot of power.

This table does not include the hugepages settings.

| Setting                                          | Effect                                                                                                                                    |
| ------------------------------------------------ | ----------------------------------------------------------------------------------------------------------------------------------------- |
| `isolcpus=8,9`                                   | Isolate the specified CPU cores so Linux won't schedule anything on them; replace with at least one core you will then use to run the NFs |
| `acpi=noirq`                                     | Disable ACPI interrupts                                                                                                                   |
| `nosoftlockup`                                   | Don't print backtraces when a process appears to be locked up (such as an NF that runs for a while)                                       |
| `intel_idle.max_cstate=0 processor.max_cstate=0` | Do not allow the CPU to enter low-power states                                                                                            |
| `idle=poll`                                      | Do not allow the kernel t use a wait mechanism in the idle routine                                                                        |
| `mce=ignore_ce`                                  | Ignore corrected errors that cause periodic latency spikes                                                                                |
| `intel_pstate=disable`                           | Prevents the Intel driver from managing power state and frequency                                                                         |
| `cpuidle.off=1`                                  | Disable CPU idle time management                                                                                                          |
| `pcie_aspm=off`                                  | Disable PCIe Active State Power Management, forcing PCIe devices to always run at full power                                              |
| `processor.ignore_ppc=1`                         | Ignore BIOS warnings about CPU frequency                                                                                                  |
| `intel_iommu=on iommu=pt`                        | Set the IOMMU to passthrough, required on some CPUs for DPDK's huge pages to run at full performance                                      |


# FAQ

- Q: DPDK says `No free hugepages reported in hugepages-1048576kB`, what did I do wrong?
- A: Nothing wrong! This just means there are no 1GB hugepages; as long as it can find the 2MB ones, you're good.

- Q: DPDK says `PMD: ixgbe_dev_link_status_print():  Port 0: Link Down`, what's up?
- A: This doesn't mean the link is down, just that it's down _at the moment DPDK checks_, it usually comes up right after that and the NF is fine.

# Dependencies

We depend on, and are grateful for:

- [DPDK](https://www.dpdk.org)
- [FastClick](https://github.com/tbarbette/fastclick)
- [KLEE](https://klee.github.io), with our modifications available as [a repository in the same GitHub organization](https://github.com/vignat/klee)
- [KLEE-uClibc](https://github.com/klee/klee-uclibc)
- [Libmoon](https://github.com/libmoon/libmoon) and its associated [MoonGen](https://github.com/emmericp/MoonGen)
- [OCaml](https://ocaml.org)
- [Python](https://www.python.org)
- [VeriFast](https://people.cs.kuleuven.be/~bart.jacobs/verifast), with our modifications available as [a repository in the same GitHub organization](https://github.com/vignat/verifast)
- [Z3](https://github.com/Z3Prover/z3/wiki)


# SOSP paper details

_This section details the justification for each claim, figure, table in the SOSP paper; references are to sections of this file_

Section 1, three improvements from VigNAT:
- We generalize to arbitrary NFs -> we present five verified NFs in this repository, and it is easy to create a new one (see `Making your own NF`)
- We verify the entire stack -> you can build and verify an OS with a single NF using this repository (see DSOS-related points of `Vigor NFs`)
- We introduce pay-as-you-go verification -> you can verify an NF with any spec you want, even partial (see the pay-as-you-go part of `Vigor NFs`)

Section 1, we present five NFs and show that each performs on par with a standard baseline:
- See the list of Vigor NFs and baselines, as well as benchmarking instructions, in `Vigor NFs`

Section 2, Vigor verification has two components:
- 1, libVig verification -> this can be checked as indicated in `Vigor NFs`
- 2, NF stack verification -> this can be checked as indicated in `Vigor NFs`

Section 2, libVig provides data structures to write NFs:
- These are in the `libvig/containers` folder in this repository

Section 3, NF_EXPORT_STATE macro:
- This is a simplification of our messy prototype; see the `dataspec.ml`, `fspec.ml`, `dataspec.py` files in each NF's folder in this repository

Section 4, percents of code that ends up running:
- See the artifact from the KBNets work: https://github.com/vignat/vignat/tree/kbnets18 (specifically in the `replication/kbnets` folder)

Section 4, early OS startup code:
- Assembly instructions during boot, see the `libvig/kernel/asm` folder in this repository
- C code to scan the PCI bus, see the `libvig/kernel/dsos_pci.c` file in this repository
- Trivial memory allocator, see the `libvig/stubs/externals/malloc.c` file in this repository

Section 5, our tool provides failed symbolic traces:
- During validation (see `Vigor NFs` above), any trace printed with something other than "Invalid" can be inspected (they are in the `validator/out` folder)


Figure 1:
- "NF logic" is the code in each NF's folder in this repository
- "Packet I/O framework" is DPDK's `lib` folder
- "libVig" is in the `libvig` folder in this repository
- "Driver" is a DPDK driver; we verified `drivers/net/ixgbe`
- "NF-specific OS" is the DSOS in the `libvig/kernel` folder in this repository

Figure 2:
- "NF logic" / "libVig" / "System stack" have the same meanings as in Figure 1
- "Vigor toolchain" is composed of KLEE, VeriFast, and the Vigor Validator; the latter is in the `validator` folder in this repository
- "RFC-derived specification" are the `spec.py` files in each NF's folder in this repository
- "One-off properties" are the `paygo-*.py` files in each NF's folder in this repository

Figure 3:
- This is a simplified version of the `vigbridge/spec.py` file in this repository

Figure 4:
- "Stateless logic" and "libVig" have the same meaning as Figure 1's "NF logic" and "libVig"
- "libVig API" are the header files in the `libvig` folder in this repository
- "NF specification" has the same meaning as Figure 2's "RFC-derived specification"/"One-off properties"
- Step 1 "Symbolic execution" is performed by KLEE, using one of the `symbex` Make targets as indicated in `Vigor NFs`
- Step 2 "Conversion" is performed by the `validator/import.ml` file in this repository
- Step 3 "Lemma insertion" is performed by the `validator/common_fspec.ml` in this repository
- Step 4 "Theorem proving" is performed by VeriFast, as invoked in the `validator/verifier.ml` file in this repository

Figure 5:
- This is a simplified version of the `vigbridge` folder's code (besides the `spec.py` file), and of the `nf_main.c` file in this repository

Figure 6:
- This is a simplified version of a common pattern we use in NFs, see e.g. `vignat/nat_flowmanager.{c,h}`

Figure 7:
- This is a simplified version of the `vigbridge/paygo-learn.py` file in this repository

Figure 8:
- This is a simplified version of the `vigbridge/spec.py` file in this repository

Figure 9:
- This is a simplified version of the `vigbridge/paygo-broadcast.py` file in this repository

Figure 10:
- This is a graphical version of the setup described by the `bench/config.sh` file in this repository

Figure 11:
- SOSPTODO show detailed data, for now you just have to believe us... sorry


Table 1:
- These are the NFs mentioned in `Vigor NFs`

Table 2:
- These numbers are obtained using their corresponding targets as mentioned in `Vigor NFs`

Table 3:
- These numbers are obtained using the targets mentioned in `Vigor NFs`; note that we count traces (as reported at the end of a KLEE run), not prefixes, and that to get the per-trace time we divide the total user time by the number of traces.

Table 4:
- The NF bugs were discovered during development
- The DPDK and ixgbe bugs can be reproduced by un-patching DPDK and running verification.

Table 5:
- These numbers can be reproduced (assuming identical hardware) by running the benchmarks as described in `Vigor NFs`

Table 6:
- The "LOC" column can be obtained using the spec line-counting target as mentioned in `Vigor NFs`
- The time to translate RFCs was noted during development and is not meaningfully reproducible
- The user-supplied bounds are SOSPTODO the condition methods in each NF, let's explain this nicely and document it in the template

Table 7:
- The modular properties for each NF can be found as `paygo-*.py` files in each NF's repository
