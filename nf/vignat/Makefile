# Binary name
APP := nat

# Runtime and verification files
NF_FILES := nat_main.c nat_config.c \
            nat_flow.c nat_flowmanager.c nat_flowtable.c

# Verification files
NF_VERIF_FILES := nat_loop.c

# Verification arguments
NF_VERIF_ARGS := --lan-dev 0 \
                 --wan 1 \
                 --expire 10 \
                 --starting-port 0 \
                 --max-flows 65536 \
                 --extip 0.0.0.0 \
                 --eth-dest 0,01:23:45:67:89:00 \
                 --eth-dest 1,01:23:45:67:89:01

# Include parent (in a convoluted way cause of DPDK)
include $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/../Makefile
