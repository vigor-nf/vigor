# Binary name
APP := lb

# Need 3 devices otherwise the concept of a load-balancer doesn't make sense
NF_DEVICES := 3

# Runtime and verification files
NF_FILES := lb_main.c lb_balancer.c lb_config.c lb_flow.h.gen.c lb_backend.h.gen.c ../lib/stubs/ether_addr.h.gen.c ip_addr.h.gen.c

# Verification files
NF_VERIF_FILES := lb_loop.c

# Verification arguments
NF_VERIF_ARGS := --flow-expiration 10 \
                 --flow-capacity 65536 \
                 --backend-capacity 20 \
                 --cht-height 100 \
                 --backend-expiration 60

AUTO_GEN_FILES := lb_flow.h.gen.c lb_flow.h.gen.h \
                  lb_backend.h.gen.c lb_backend.h.gen.h \
                  ../lib/stubs/ether_addr.h.gen.c ../lib/stubs/ether_addr.h.gen.h \
                  ip_addr.h.gen.c ip_addr.h.gen.h \
                  lb_loop.h lb_loop.c


all: $(AUTO_GEN_FILES) $(APP)

# Include parent (in a convoluted way cause of DPDK)
include $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/../Makefile

lb_flow.h.gen.c lb_flow.h.gen.h: lb_flow.h
	bash ../../codegen/generate.sh lb_flow.h

lb_backend.h.gen.c lb_backend.h.gen.h ../lib/stubs/ether_addr.h.gen.c ../lib/stubs/ether_addr.h.gen.h: lb_backend.h ../lib/stubs/ether_addr.h
	bash ../../codegen/generate.sh lb_backend.h

ip_addr.h.gen.c ip_addr.h.gen.h: ip_addr.h
	bash ../../codegen/generate.sh ip_addr.h

lb_loop.h lb_loop.c: lb_data_spec.ml
	bash ../../codegen/gen-loop-boilerplate.sh lb_data_spec.ml
