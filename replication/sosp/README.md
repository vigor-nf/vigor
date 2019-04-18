### Lines of Code

In an NF directory, e.g. `nf/vignat`, run:

- `make loc` for the lines of code of the NF itself
- `make loc-dpdk` for the lines of code of the NF plus DPDK and its driver
- `make loc-dsos` for the lines of code of the entire stack: NF, DPDK, driver, DSOS
- `make loc-libvig` for the lines of code and proof annotations in the data structures library

In the `validator` folder, run `make loc-spec` for the lines of code in each spec.
