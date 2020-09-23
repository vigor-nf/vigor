 This folder contains patches and configuration files for dependencies of the Vigor toolchain, namely:
- DPDK patches
  - `memalloc` fixes memory bug found in DPDK
  - `config` patches the DPDK default config
- DPDK patches for the `ixgbe` driver:
  - `avoid_bit_bang` avoids unnecessary usage of bit-banging during initialization
  - `no_rxen_on_fctrl_write` ensures the FCTRL bit is written to according to the spec (reported)
  - `rdrxctl_special_writes` fixes a write to RDRXCTL according to the specification (reported)
  - `unknown_eimc_bit` removes the usage of an undocumented bit in the EIMC register (reported)
  - `unknown_ralrah` fixes the usage of undocumented Receive Address Low/High registers
     I didn't want to copy/paste the enormous function. THIS MAKES IXGBE ONLY WORK WITH THE 82599!!!
  - `unknown_swfw_sync_bit` removes the usage of an undocumented bit in the SWFW_SYNC (a.k.a. GSSR) register (reported)
  - `wrong_register_dpf_pmcf` removes the usage of bits that should be in another register on the 82599
  - `hacks` contains unfortunate hacks for verification :-( (There is an `ideal` file for the patch we want, but can't make work)
- A minimalistic config file for `klee-uclibc`


### Notes about the ixgbe hacks

The issue is a combination of how DPDK manages mbufs and how Vigor does havocing.

Roughly speaking, DPDK's ixgbe maintains a cache of mbufs to receive data into, so it doesn't have to get one from the pool each time; and it gives back mbufs into the pool when they are done being written out. (Surprisingly, this is done right before sending mbufs, not right after)

The issue is then that Vigor will havoc the entire mbuf cache, and even the pool, which will mess everything up since Vigor's havocing replaces values with unconstrained symbols so the internal state of the pool will make no sense and cause symbolic indexing.

To avoid this, we do not allow DPDK to get mbufs from the pool in the main loop, or to put mbufs back into it; even free doesn't do it.

This means that we assume the mempool behaves correctly during the main loop - not a very strong assumption given that the "get" and "put" code paths are already used during init.
