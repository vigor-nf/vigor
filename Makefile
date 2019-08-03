# Skeleton Makefile for Vigor NFs
# Variables that should be defined by inheriting Makefiles:
# - NF_DEVICES := <number of devices during verif-time, default 2>
# - NF_FILES := <NF files for both runtime and verif-time>
# - NF_VERIF_ARGS := <arguments to pass to the NF at verif-time>

# -----------------------------------------------------------------------

# get current dir
# see https://stackoverflow.com/a/8080530
SELF_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))

# Default value for devices
NF_DEVICES ?= 2

# If KLEE paths are not defined (eg because the user installed deps themselves), try to compute it based on KLEE_INCLUDE.
KLEE_BUILD_PATH ?= $(KLEE_INCLUDE)/../build
KLEE_UCLIBC ?= $(KLEE_INCLUDE)/../../klee-uclibc


# DPDK stuff
include $(RTE_SDK)/mk/rte.vars.mk

# Same name for everyone, makes it easier to run them all with the same script
APP := nf

# allow the use of advanced globs in paths
SHELL = /bin/bash -O extglob -O globstar -c

# Add the state file to the NF sources
NF_FILES += state.c

# NF base source
SRCS-y := $(SELF_DIR)/nf_main.c \
          $(SELF_DIR)/lib/nf_time.c \
          $(SELF_DIR)/lib/nf_util.c \
          $(SELF_DIR)/lib/expirator.c \
          $(SELF_DIR)/lib/containers/double-chain.c $(SELF_DIR)/lib/containers/double-chain-impl.c \
          $(SELF_DIR)/lib/containers/map.c $(SELF_DIR)/lib/containers/map-impl.c \
          $(SELF_DIR)/lib/containers/double-map.c \
          $(SELF_DIR)/lib/containers/vector.c \
          $(SELF_DIR)/lib/containers/cht.c \
          $(SELF_DIR)/lib/packet-io.c
# NF specific source
SRCS-y += $(NF_FILES)

# compiler flags
CFLAGS += -I $(SELF_DIR)
CFLAGS += -std=gnu99
CFLAGS += -O3
#CFLAGS += -O0 -g -rdynamic -DENABLE_LOG -Wfatal-errors

# DPDK stuff
include $(RTE_SDK)/mk/rte.extapp.mk

### VeriFast verification ###
LIBVIG_SRC_ARITH := $(SELF_DIR)/lib/containers/arith.c \
                    $(SELF_DIR)/lib/containers/modulo.c
LIBVIG_SRC_Z3 := $(subst .c,.o,$(LIBVIG_SRC_ARITH)) \
                 $(SELF_DIR)/lib/containers/bitopsutils.c \
                 $(SELF_DIR)/lib/containers/mod_pow2.c \
                 $(SELF_DIR)/lib/containers/lpm-dir-24-8-lemmas.c \
                 $(SELF_DIR)/lib/containers/lpm-dir-24-8.c
LIBVIG_SRC := $(subst .c,.o,$(LIBVIG_SRC_Z3)) \
              $(SELF_DIR)/lib/containers/double-chain-impl.c \
              $(SELF_DIR)/lib/containers/double-chain.c \
              $(SELF_DIR)/lib/containers/map-impl.c \
              $(SELF_DIR)/lib/containers/map-impl-pow2.c \
              $(SELF_DIR)/lib/containers/double-map.c \
              $(SELF_DIR)/lib/containers/vector.c \
              $(SELF_DIR)/lib/containers/prime.c \
              $(SELF_DIR)/lib/containers/listutils-lemmas.c \
              $(SELF_DIR)/lib/containers/transpose-lemmas.c \
              $(SELF_DIR)/lib/containers/permutations.c \
              $(SELF_DIR)/lib/containers/cht.c \
              $(SELF_DIR)/lib/packet-io.c \
              $(SELF_DIR)/lib/containers/map.c \
              $(SELF_DIR)/lib/coherence.c \
              $(SELF_DIR)/lib/expirator.c

VERIFAST_COMMAND := verifast -I $(SELF_DIR) -I $(SELF_DIR)/lib/stubs/dpdk -allow_assume -shared
VERIFAST_CLEAN_COMMAND := rm -rf $(SELF_DIR)/**/*.vfmanifest
verifast:
	@printf '\n\n!!!\n\n'
	@printf 'This is gonna take a while, go make a nice cup of tea...\n\n'
	@printf 'Note that we are verifying the code twice, once with the power-of-two optimization for the map and once without\n'
	@printf 'Also, some parts of the proof can only be verified with Z3 and some with the standard VeriFast solver, so we split the verification in parts...\n'
	@printf '\n!!!\n\n'
	@$(VERIFAST_CLEAN_COMMAND)
	@$(VERIFAST_COMMAND) -emit_vfmanifest $(LIBVIG_SRC_ARITH)
	@$(VERIFAST_COMMAND) -prover="Z3v4.5" -emit_vfmanifest $(LIBVIG_SRC_Z3)
	@$(VERIFAST_COMMAND) -emit_vfmanifest $(LIBVIG_SRC)
	@$(VERIFAST_COMMAND) -emit_vfmanifest -D CAPACITY_POW2 $(LIBVIG_SRC)


### KLEE verification ###

# Basic flags: only compile, emit debug code, in LLVM format, with checks for overflows
#              (but not unsigned overflows - they're not UB and DPDK depends on them)
VERIF_FLAGS := -c -g -emit-llvm -fsanitize=signed-integer-overflow

# Basic includes: NF root and KLEE
VERIF_INCLUDES := -I $(SELF_DIR) -I $(KLEE_INCLUDE)
# ...and the DPDK cmdline library
VERIF_INCLUDES += -I $(RTE_SDK)/lib/librte_cmdline

# NF args for the verification
NF_VERIF_BASE_ARGS := nf.bc --no-shconf --

# Convert the bash-style NF arguments (nf --no-shconf -- -n 3 -m 6) into
# C-style char*[] comma separated list
# of c-strings ("nf","--no-shconf","--","-n","3","-m","6") for DSOS to put
# into argv at compilation time.
dquote=\"
NF_ARGUMENTS_MACRO=-DNF_ARGUMENTS=\"$(subst $(space),$(dquote)$(comma)$(dquote),$(NF_VERIF_BASE_ARGS) $(NF_VERIF_ARGS))\"

# Defines. TODO remove _GNU_SOURCE from here, #define it in files
VERIF_DEFS := -D_GNU_SOURCE -DKLEE_VERIFICATION
# Number of devices
VERIF_DEFS += -DSTUB_DEVICES_COUNT=$(NF_DEVICES)

# Basic files
# NF base
VERIF_FILES := $(SELF_DIR)/nf_main.c $(SELF_DIR)/lib/nf_util.c
# Specific NF
VERIF_FILES += $(NF_FILES)
# NF base stubs
VERIF_FILES += $(SELF_DIR)/lib/stubs/containers/!(batcher)-stub.c $(SELF_DIR)/lib/stubs/*-stub.c
# NF loop file
VERIF_FILES += loop.c
# Environment stubs
VERIF_FILES += $(SELF_DIR)/lib/stubs/externals/*.c $(SELF_DIR)/lib/stubs/core_stub.c $(SELF_DIR)/lib/stubs/time_stub.c
# DPDK cmdline parsing library, always included, we don't want/need to stub it
VERIF_FILES += $(RTE_SDK)/lib/librte_cmdline/*.c
# ...and the string function it uses
VERIF_FILES += $(RTE_SDK)/lib/librte_eal/common/eal_common_string_fns.c

# Defines for DPDK
# CPUFLAGS is set to a sentinel value; usually it's passed from the DPDK build system
VERIF_DPDK_DEFS := -DRTE_COMPILE_TIME_CPUFLAGS=424242

# Includes for DPDK
# We need librte_eal/common because eal_private.h is in there, required by eal_thread.c...
# We need bus/pci because the linuxapp PCI stuff requires a private.h file in there...
# bus/vdev and net/ixgbe are for stub drivers (which are vdevs) and hardware (the ixgbe driver) respectively
VERIF_DPDK_INCLUDES := -I $(RTE_SDK)/$(RTE_TARGET)/include \
			-I $(RTE_SDK)/lib/librte_eal/common \
			-I $(RTE_SDK)/drivers/bus/vdev \
			-I $(RTE_SDK)/drivers/bus/pci \
			-I $(RTE_SDK)/drivers/net/ixgbe
# And then some special DPDK includes: builtin_stubs for built-ins DPDK uses
VERIF_DPDK_INCLUDES += --include=lib/stubs/builtin_stub.h --include=rte_config.h

# Files for DPDK
# Low-level stubs for specific functions
VERIF_DPDK_FILES := $(SELF_DIR)/lib/stubs/dpdk_low_level_stub.c
# Platform-independent and Linux-specific EAL
VERIF_DPDK_FILES += $(RTE_SDK)/lib/librte_eal/common/*.c $(RTE_SDK)/lib/librte_eal/linuxapp/eal/*.c
# Default ring mempool driver
VERIF_DPDK_FILES += $(RTE_SDK)/drivers/mempool/ring/rte_mempool_ring.c
# Other libraries, except acl and distributor which use CPU intrinsics (there is a generic version of distributor, but we don't need it),
# and power has been broken for a while: http://dpdk.org/ml/archives/dev/2016-February/033152.html
VERIF_DPDK_FILES += $(RTE_SDK)/lib/!(librte_acl|librte_distributor|librte_power)/*.c
# Virtual devices support (for stub drivers)
VERIF_DPDK_FILES += $(RTE_SDK)/drivers/bus/vdev/*.c
# PCI driver support (for ixgbe driver)
VERIF_DPDK_FILES += $(RTE_SDK)/drivers/bus/pci/*.c $(RTE_SDK)/drivers/bus/pci/linux/*.c
# ixgbe driver
VERIF_DPDK_FILES += $(RTE_SDK)/drivers/net/ixgbe/ixgbe_{fdir,flow,ethdev,ipsec,pf,rxtx,tm}.c $(RTE_SDK)/drivers/net/ixgbe/base/ixgbe_{api,common,phy,82599}.c

# Commands
# Cleanup
CLEAN_COMMAND := rm -rf build *.bc *.os {loop,state}.{c,h} $(SELF_DIR)/**/*.gen.{c,h}
# Compilation
COMPILE_COMMAND := clang
# Linking with klee-uclibc, but without some methods we are stubbing (not sure why they're in klee-uclibc.bca)
LINK_COMMAND := llvm-ar x $(KLEE_BUILD_PATH)/Release+Debug+Asserts/lib/klee-uclibc.bca && \
                rm -f sleep.os vfprintf.os && \
                llvm-link -o nf_raw.bc  *.os *.bc
# Optimization; analyze and remove as much provably dead code as possible (exceptions are stubs; also, mem* functions, not sure why it DCEs them since they are used...maybe related to LLVM having intrinsics for them?)
# I've tried adding '-constprop -ipconstprop -ipsccp -correlated-propagation -loop-deletion -dce -die -dse -adce -deadargelim -instsimplify'; this works but the traced prefixes seem messed up :(
OPT_EXCEPTIONS := memset,memcpy,memmove,stub_abort,stub_free,stub_hardware_read,stub_hardware_write,stub_prefetch,stub_rdtsc,stub_socket,stub_strerror,stub_delay
OPT_COMMAND := opt -basicaa -basiccg -internalize -internalize-public-api-list=main,$(OPT_EXCEPTIONS) -globaldce nf_raw.bc > nf.bc
# KLEE verification
# if something takes longer than expected, try --max-solver-time=3 --debug-report-symbdex (to avoid symbolic indices)
VERIF_COMMAND := /usr/bin/time -v \
                 klee -no-externals -allocate-determ -allocate-determ-start-address=0x00040000000 -allocate-determ-size=1000 -dump-call-traces -dump-call-trace-prefixes -solver-backend=z3 -exit-on-error -max-memory=750000 -search=dfs -condone-undeclared-havocs --debug-report-symbdex

clean-vigor:
	@$(CLEAN_COMMAND)

clean: clean-vigor

# DPDK's weird makefiles call this twice, once in the proper dir and once in build/, we only care about the former
autogen:
	@if [ '$(notdir $(shell pwd))' != 'build' ]; then \
	  $(SELF_DIR)/codegen/generate.sh $(NF_AUTOGEN_SRCS) $(SELF_DIR)/lib/stubs/ether_addr.h; \
	  $(SELF_DIR)/codegen/gen-loop-boilerplate.sh dataspec.ml; \
	fi

# Built-in DPDK default target, make it aware of autogen
all: autogen

symbex: clean autogen
	@$(COMPILE_COMMAND) $(VERIF_DEFS) -DVIGOR_STUB_DPDK $(VERIF_INCLUDES) -I $(SELF_DIR)/lib/stubs/dpdk $(VERIF_FILES) $(VERIF_FLAGS)
	@$(LINK_COMMAND)
	@$(OPT_COMMAND)
	@$(VERIF_COMMAND) $(NF_VERIF_BASE_ARGS) $(NF_VERIF_ARGS)

symbex-fullstack: clean autogen
	@$(COMPILE_COMMAND) $(VERIF_DEFS) $(VERIF_DPDK_DEFS) -DVIGOR_STUB_HARDWARE $(VERIF_INCLUDES) $(VERIF_DPDK_INCLUDES) $(VERIF_FILES) $(VERIF_DPDK_FILES) $(SELF_DIR)/lib/stubs/hardware_stub.c $(VERIF_FLAGS)
	@$(LINK_COMMAND)
	@$(OPT_COMMAND)
	@$(VERIF_COMMAND) $(NF_VERIF_BASE_ARGS) $(NF_VERIF_ARGS)

verify-dsos-nf.bc: clean autogen
	$(COMPILE_COMMAND) $(VERIF_DEFS) $(VERIF_DPDK_DEFS) $(NF_ARGUMENTS_MACRO) -DVIGOR_STUB_HARDWARE -DDSOS -D__linux__ -libc=none $(VERIF_INCLUDES) $(VERIF_DPDK_INCLUDES) $(VERIF_FILES) $(VERIF_DPDK_FILES) $(SELF_DIR)/lib/stubs/hardware_stub.c $(SELF_DIR)/lib/kernel/*.c $(VERIF_FLAGS) -mssse3 -msse2 -msse4.1
	ar x $(KLEE_UCLIBC)/lib/libc.a
	rm -f sleep.os vfprintf.os socket.os exit.os fflush.os fflush_unlocked.os
	llvm-link -o nf_raw.bc  *.os *.bc
	$(OPT_COMMAND)

verify-dsos: verify-dsos-nf.bc
	$(VERIF_COMMAND) $(NF_VERIF_BASE_ARGS) $(NF_VERIF_ARGS)
	$(CLEAN_COMMAND)



# ################# #
# LoC count targets #
# ################# #

# cloc instead of sloccount because the latter does not report comments, and all VeriFast annotations are comments

count-loc: autogen
	@cloc $(SRCS-y) $(AUTO_GEN_FILES)

count-fullstack-loc: autogen
	@cloc $(SRCS-y) $(AUTO_GEN_FILES) $(VERIF_DPDK_FILES)

count-spec-loc:
	@cloc spec.py

count-lib-loc:
	@# Bit of a hack for this one, cloc can't be given a custom language but for some reason it knows about Pig Latin, which is never gonna happen in our codebase, so...
	@cloc --quiet --force-lang 'Pig Latin',gh  $(subst .o,.c,$(LIBVIG_SRC)) $(SELF_DIR)/lib/containers/*.gh | sed 's/Pig Latin/VeriFast /g'
	@echo "NOTE: Annotations == VeriFast code + C comments - $$(grep '//[^@]' $(subst .o,.c,$(LIBVIG_SRC)) | wc -l) (that last number is the non-VeriFast C comments)"
	@if grep -F '/*' $(subst .o,.c,$(LIBVIG_SRC)) | grep -vF '/*@'; then echo 'ERROR: There are multiline non-VeriFast comments in the C code, the total above is wrong!'; fi
