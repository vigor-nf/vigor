# Need 3 devices otherwise the concept of a load-balancer doesn't make sense
NF_DEVICES := 3

# Runtime and verification files
NF_FILES := lb_main.c lb_balancer.c lb_config.c

NF_AUTOGEN_SRCS := lb_flow.h lb_backend.h ip_addr.h

# Verification arguments
# CHT height must be a prime number
NF_VERIF_ARGS := --flow-expiration 10 \
                 --flow-capacity 65536 \
                 --backend-capacity 32 \
                 --cht-height 97 \
                 --backend-expiration 60

# Include parent (in a convoluted way cause of DPDK)
include $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/../Makefile
