NF_FILES := nop_main.c nat_config.c

NF_ARGS := --lan-dev 0 \
           --wan 1 \
           --eth-dest 0,$(or $(TESTER_MAC_EXTERNAL),01:23:45:67:89:00) \
           --eth-dest 1,$(or $(TESTER_MAC_INTERNAL),01:23:45:67:89:01)

NF_LAYER := 4

# Include parent (in a convoluted way cause of DPDK)
NF_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
include $(NF_DIR)/../Makefile.common
