NF_FILES := nop_main.c nat_config.c

# "Verification" arguments
NF_VERIF_ARGS := --lan-dev 0 \
                 --wan 1 \
                 --eth-dest 0,01:23:45:67:89:00 \
                 --eth-dest 1,01:23:45:67:89:01

# Include parent (in a convoluted way cause of DPDK)
include $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/../Makefile
