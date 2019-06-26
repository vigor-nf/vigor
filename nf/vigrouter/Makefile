# Runtime and verification files
NF_FILES := router.c parse_utils.c \
          ../nf_main.c \
          ../lib/nf_util.c \
          ../lib/packet-io.c \
          ../lib/nf_time.c \
          ../lib/containers/double-chain-impl.c \
          ../lib/containers/double-chain.c \
	  	  ../lib/containers/lpm-dir-24-8.c

AUTO_GEN_FILES := ???

# Must generate the flow.h* files before building the app
all: $(AUTO_GEN_FILES) $(APP)

# Verification files
NF_VERIF_FILES := ???

# Verification arguments
NF_VERIF_ARGS := ???

# Include parent (in a convoluted way cause of DPDK)
include $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/../Makefile
