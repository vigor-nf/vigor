# Binary name
APP := lb

# Runtime and verification files
NF_FILES := lb_main.c lb_balancer.c lb_config.c \
            ../lib/flow.c ../lib/flow-log.c \
            ../lib/flowmanager.c ../lib/flowtable.c

# Verification files
NF_VERIF_FILES := lb_loop_stub.c

# Verification arguments
NF_VERIF_ARGS := --dev-ext 0 \
                 --dev-int 1 \
                 --expire 10 \
                 --starting-port 0 \
                 --max-flows 65536 \
                 --backend 0.0.0.0 \
                 --backend 1.1.1.1 \
                 --eth-dest 0,01:23:45:67:89:00 \
                 --eth-dest 1,01:23:45:67:89:01

# Include parent (in a convoluted way cause of DPDK)
include $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/../Makefile
