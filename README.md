This repository contains the Vigor verification toolchain and network functions (NFs).

# Machine prerequisites

Our scripts assume you are using Ubuntu 18.04 or 20.04, with an active Internet connection to download dependencies.
Older Ubuntus, or other Debian-based distros, may work but have not been tested.

> :information_source: If you run the scripts in a Docker container, launch it as `--privileged` to allow opam to create namespaces. (see ocaml/opam#3498)

As an alternative to installing the dependencies on your own machine, we provide a Docker image: `dslabepfl/vigor-20.08`.
(The image `dslabepfl/vigor` corresponding to the artifact-evaluated version, using DPDK 17.11, is still available.)
However, you must still use Ubuntu 18.04 as a host, since the guest uses the host's kernel and DPDK needs kernel headers to compile.
This image can be generated with the `./Docker-build.sh` script.

_Please note that running the setup.sh script can take an hour, since it downloads and compiles many dependencies, and uses `sudo` which will prompt for your credentials._

To **compile and run** Vigor NFs, you need:

- 20 GB of disk space
- 16 GB of RAM, 8 GB of which is allocated as 4096x2MB hugepages; see the [DPDK documentation](https://doc.dpdk.org/guides/linux_gsg/sys_reqs.html#linux-gsg-hugepages) to set up hugepages.
- A DPDK-compatible NIC with at least two ports, bound to DPDK using the `dpdk-devbind.py` tool.
- To run `setup.sh no-verify`.

To **verify** NFs using **DPDK models**, you need:

- 20 GB of disk space
- 8 GB of RAM
- To run `setup.sh` (no arguments)

To **verify** NFs using **hardware models**, you need:

- 20 GB of disk space
- 128 GB of RAM
- To run `setup.sh` (no arguments)

To **benchmark** Vigor NFs, you need:

- One 'device under test' machine with the setup described for compiling and running NFs, and a kernel setup for performance (see the `Linux setup for performance` section below)
- One 'tester' machine, with at least two ports on a DPDK-compatible NIC, each connected to the 'device under test' ports
- Key-based SSH access to the tester from the device under test (_This is not strictly required, but will save you from entering your password many times_)
- To change the `bench/config.sh` file to match the two machines' configuration


# Vigor NFs

There are currently six Vigor NFs:

| NF            | Folder      | Description                                                                                                                         |
| ------------- | ----------- | ----------------------------------------------------------------------------------------------------------------------------------- |
| NOP           | `vignop`    | No-op forwarder                                                                                                                     |
| NAT           | `vignat`    | NAT according to [RFC 3022](https://www.ietf.org/rfc/rfc3022.txt)                                                                   |
| Bridge        | `vigbridge` | Bridge with MAC learning according to [IEEE 802.1Q-2014](https://ieeexplore.ieee.org/document/6991462) sections 8.7 and 8.8         |
| Load balancer | `viglb`     | Load balancer inspired by Google's [Maglev](https://ai.google/research/pubs/pub44824)                                               |
| Policer       | `vigpol`    | Traffic policer whose specification we invented                                                                                     |
| Firewall      | `vigfw`     | Firewall whose specification we invented                                                                                            |

There are additional "baseline" NFs, which can _only be compiled, run and benchmarked_, each in its own folder:

| NF                  | Folder              | Description                            |
| ------------------- | ------------------- | -------------------------------------- |
| Click NOP           | `click-nop`         | Click-based no-op forwarder            |
| Click NAT           | `click-nat`         | Click-based NAT                        |
| Click bridge        | `click-bridge`      | Click-based MAC learning bridge        |
| Click load balancer | `click-lb`          | Click-based load balancer (not Maglev) |
| Moonpol             | `moonpol`           | Libmoon-based traffic policer          |
| Click firewall      | `click-fw`          | Click-based firewall                   |

The Click- and Libmoon-based NFs use batching if the `VIGOR_USE_BATCH` environment variable is set to `true` when running the benchmark targets (see table below).


Pick the NF you want to work with by `cd`-ing to its folder, then use one of the following `make` targets:

| Target(s)                  | Description                                       | Expected duration                  |
| -------------------------- | ------------------------------------------------- | ---------------------------------- |
| Default                    | Compile the NF                                    | <1min                              |
| `run`                      | Run the NF using recommended arguments            | <1min to start (stop with Ctrl+C)  |
| `symbex validate`          | Verify the NF only                                | <1min to symbex, <1h to validate   |
| `symbex-withdpdk validate` | Verify the NF + DPDK + driver                     | <1h to symbex, hours to validate   |
| `symbex-withnfos validate` | Verify the NF + DPDK + driver + NFOS (full stack) | <1h to symbex, hours to validate   |
| `count-loc`                | Count LoC in the NF                               | <1min                              |
| `count-spec-loc`           | Count LoC in the specification                    | <1min                              |
| `count-nfos-loc`           | Count LoC in the NFOS                             | <1min                              |
| `count-libvig-loc`         | Count LoC in libVig                               | <1min                              |
| `count-dpdk-loc`           | Count LoC in DPDK (not drivers)                   | <1min                              |
| `count-ixgbe-loc`          | Count LoC in the ixgbe driver                     | <1min                              |
| `count-uclibc-loc`         | Count LoC in KLEE-uClibc                          | <1min                              |
| `benchmark-throughput`     | Benchmark the NF's throughput                     | <15min                             |
| `benchmark-latency`        | Benchmark the NF's latency                        | <5min                              |
| `nfos-iso`                 | Build a NFOS ISO image runnable in a VM           | <1min                              |
| `nfos-multiboot1`          | Build a NFOS ISO image suitable for netboot       | <1min                              |
| `nfos-run`                 | Build and run NFOS in a qemu VM                   | <1min to start                     |



To run with your own arguments, compile then run `sudo ./build/app/nf -- -?` which will display the command-line arguments you need to pass to the NF.

To verify using a pay-as-you-go specification, add `VIGOR_SPEC=paygo-your_spec.py` before a verification command; the spec name must begin with `paygo-` and end with `.py`.

For instance:
- To verify the "broadcast" pay-as-you-go property of the Vigor bridge (without verifying DPDK or the NFOS), run `cd vigbridge` then `VIGOR_SPEC=paygo-broadcast.py make symbex validate`.
- To benchmark the Vigor policer's throughput, run `cd vigpol` then `make benchmark-throughput`


# Create your own Vigor NF

- Run `make new-nf` at the root of the repository, and answer the prompt.

The generated files contain inline comments describing how to write your NF code and your specification.


# Repository structure

Besides the NF folders mentioned above, the repository contains:
- `.git*`: Git-related files
- `.clang-format`: Settings file for the clang-format code formatter
- `.travis*`: Travis-related files for continuous integration
- `Docker*` Docker-related files to build an image
- `Makefile*`: Makefiles for the NFs
- `README.md`: This file
- `bench`: Benchmarking scripts, used by the benchmarking make targets
- `codegen`: Code generators, used as part of the Vigor build process
- `doc`: Documentation files
- `grub.cfg`, `linker.ld`, `pxe-boot.sh`: NFOS-related files
- `libvig`: The libVig folder, containing `verified` code, `proof` code, `models`, and the NFOS `kernel`
- `nf.{h,c}`, `nf-util.{h,c}`, `nf-log.h`: Skeleton code for Vigor NFs
- `setup*`: Setup script and related files
- `template`: Template for new Vigor NFs (see "Create your own Vigor NF" above)
- `validator`: The Vigor Validator


# Using the NFOS

Vigor includes a NF OS that is simple enough to be symbolically executed, besides trusted boot code.

You can run NFOS either in a virtual machine, using qemu, or on bare metal, using PXE boot.

Note, that as NFOS can not read cmdline arguments, all the NF arguments are compiled into the image during the build.
You can set the NF arguments in the respective NF Makefile.

## Running the NFOS in a VM

In order to run the NFOS inside a virtual machine, you need your kernel allow direct device access through VFIO.
For that you need to pass `intel_iommu=on iommu=pt` to your linux kernel in the command line arguments in your bootloader.

Further, you need to load the vfio-pci module to forward your NICs to the VM with ;

    $ modprobe vfio-pci

Then, bind the NICs you intend for the NF to use to `vfio-pci` (`RTE_SDK` is the path to your DPDK folder):

    $ $RTE_SDK/usertools/dpdk-devbind.py -b vfio-pci <nic1> <nic2>
    
Here `<nic1>` and `<nic2>` are PCI addresses of the NICs you want to bind (e.g. `0000:06:00.0`).
You can find the PCI addresses of your NICs using `dpdk-devbind.py -s`.

> :warning: **Warning**: after the next step your terminal will stop responding.
> Make sure you have a spare terminal open on this machine.

Finally, to run the NF with NFOS in a VM, get in to the NF directory, e.g. `vigor/vignat`, and run:

    $ make nfos-run
    
This will build the NF with DPDK, device driver and NFOS, produce the bootable ISO image and start
a qemu machine executing that image.
Note that NFOS ignores any input, so your terminal will show the NFOS output and will stop responding.
You will need to kill the qemu process from a different terminal.

## Running the NFOS on bare metal over the network

In order to run the NFOS on bare metal you will need an extra ethernet connection of the machine intended to run the NFOS (we call it DUT from now on) and a PXE server machine.

You will need `nfos-x86_64-multiboot1.bin` image on the machine that will serve PXE requests.
You can build it either directly on the machine, or build it on DUT and copy it over.
To build the image, run:

    $ make nfos-multiboot1
    
To serve the image, run on the machine intended as a PXE server:

    $ ./pxe-boot.sh nfos-x86_64-multiboot1.bin
    
This will start a DHCP server and a PXE server and wait for network boot requests.
As our image is larger than 64KB, we use a two step boot process, booting first an ipxe/undionly.kpxe image that
then fetches the NFOS image and boots it.

In BIOS, configure DUT to boot from network, using the interface connected to the PXE server.
When you reboot it, you should see some activity in the PXE server output and see NFOS output on DUT (printing the NF configuration).
At this point you can stop the PXE boot server.
The NFOS is running!


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

- Q: DPDK cannot reserve all of the hugepages it needs, though it can reserve some of them.
- A: Reboot the machine. This is the only workaround that always works.


# Dependencies

We depend on, and are grateful for:

- [DPDK](https://www.dpdk.org)
- [FastClick](https://github.com/tbarbette/fastclick)
- [KLEE](https://klee.github.io), with our modifications available as [a repository in the same GitHub organization](https://github.com/vigor-nf/klee)
- [KLEE-uClibc](https://github.com/klee/klee-uclibc)
- [Libmoon](https://github.com/libmoon/libmoon) and its associated [MoonGen](https://github.com/emmericp/MoonGen)
- [OCaml](https://ocaml.org)
- [Python](https://www.python.org)
- [VeriFast](https://people.cs.kuleuven.be/~bart.jacobs/verifast), with our modifications available as [a repository in the same GitHub organization](https://github.com/vigor-nf/verifast)
- [Z3](https://github.com/Z3Prover/z3/wiki)


# SOSP paper details

This section details the justification for each figure and table in the SOSP paper; "references" are to sections of this file, `paths` refers to this repository unless otherwise indicated.

Figure 1:
- "NF logic" is the code in each NF's folder
- "Packet I/O framework" is the `lib` folder in [the DPDK 17.11 repository](https://git.dpdk.org/dpdk/tree/?h=v17.11)
- "libVig" is in `libvig`
- "Driver" is a DPDK driver; we verified `drivers/net/ixgbe` in [the DPDK 17.11 repository](https://git.dpdk.org/dpdk/tree/?h=v17.11)
- "NF-specific OS" is the NFOS in `libvig/kernel`

Figure 2:
- "NF logic" / "libVig" / "System stack" have the same meanings as in Figure 1
- "Vigor toolchain" is composed of KLEE, VeriFast, and the Vigor Validator; the latter is in `validator`
- "RFC-derived specification" are the `spec.py` files in each NF's folder
- "One-off properties" are the `paygo-*.py` files in each NF's folder

Figure 3:
- This is a simplified version of `vigbridge/spec.py`

Figure 4:
- "Stateless logic" and "libVig" have the same meaning as Figure 1's "NF logic" and "libVig"
- "libVig API" are the header files in the `libvig` folder
- "NF specification" has the same meaning as Figure 2's "RFC-derived specification"/"One-off properties"
- Step 1 "Symbolic execution" is performed by KLEE, using one of the `symbex` Make targets as indicated in [Vigor NFs](#vigor-nfs)
- Step 2 "Conversion" is performed by `validator/import.ml`
- Step 3 "Lemma insertion" is performed by `validator/common_fspec.ml`
- Step 4 "Theorem proving" is performed by VeriFast, as invoked in `validator/verifier.ml`

Figure 5:
- This is a simplified version of the `vigbridge` folder's code (besides `spec.py` and `paygo-*.py`), and of `nf_main.c`

Figure 6:
- This is a simplified version of a common pattern we use in NFs, see e.g. `vignat/nat_flowmanager.{c,h}`

Figure 7:
- This is a simplified version of `vigbridge/paygo-learn.py`

Figure 8:
- This is a simplified version of `vigbridge/spec.py`

Figure 9:
- This is a simplified version of `vigbridge/paygo-broadcast.py`

Figure 10:
- This is a made-up example for the paper, using standard Vigor spec syntax.

Figure 11:
- This is a graphical version of the setup described by `bench/config.sh`

Figure 12:
- The data is in `doc/VigorClickComponentsComparison.csv` file


Table 1:
- These are the NFs mentioned in [Vigor NFs](#vigor-nfs)

Table 2:
- These numbers are obtained using their corresponding targets as mentioned in [Vigor NFs](#vigor-nfs)

Table 3:
- This is an outdated version of Table 8; use `patch -R < optimize.patch` in each NF's folder to revert the optimization if you want to reproduce these numbers;
  note that they do not validate any more, sometimes because the specs assume that the NF always expire flows, but the unoptimized NFs do not,
  sometimes because the types of variables changed a bit.
  Thus, we extrapolated the time of the "valid" and "assertion failed" traces to the "type mismatch" traces,
  since type mismatches take almost no time to detect compared to the time it takes to verify a trace.

Table 4:
- The NF bugs were discovered during development
- The DPDK and ixgbe bugs can be reproduced by un-patching DPDK and running verification.

Table 5:
- These numbers can be reproduced (assuming identical hardware) by running the benchmarks as described in [Vigor NFs](#vigor-nfs)

Table 6:
- The "LOC" column can be obtained using the spec line-counting target as mentioned in [Vigor NFs](#vigor-nfs)
- The time to translate RFCs was noted during development and is not meaningfully reproducible
- The user-supplied bounds are the conjunctions of the methods passed as the last argument of a data structure declaration in the `fspec.ml` file of each NF;
  except that to be consistent with the paper, `a < X & X < b` counts as 1.

Table 7:
- The modular properties for each NF can be found as `paygo-*.py` files in each NF's repository

Table 8:
- These numbers are obtained using the targets mentioned in [Vigor NFs](#vigor-nfs);
  note that we count paths (as reported at the end of a KLEE run), not prefixes, and that to get the per-trace time we multiply wall-clock time by the number of CPUs used by `parallel` then divide by the number of paths.
