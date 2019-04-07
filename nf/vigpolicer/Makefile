# Binary name
APP := policer

# Runtime and verification files
NF_FILES := policer_main.c policer_config.c dynamic_value.h.gen.c ../lib/stubs/ether_addr.h.gen.c ip_addr.h.gen.c policer_state.c

AUTO_GEN_FILES := dynamic_value.h.gen.c dynamic_value.h.gen.h \
                  ip_addr.h.gen.c ip_addr.h.gen.h \
                  ../lib/stubs/ether_addr.h.gen.c ../lib/stubs/ether_addr.h.gen.h \
                  policer_loop.h policer_loop.c \
                  policer_state.h policer_state.c


all: $(AUTO_GEN_FILES) $(APP)

# Verification files
NF_VERIF_FILES := policer_loop.c

# Verification arguments
NF_VERIF_ARGS := --lan 0 --wan 1 --rate 12500 --burst 125000 --capacity 100

# Include parent (in a convoluted way cause of DPDK)
include $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/../Makefile

dynamic_value.h.gen.c dynamic_value.h.gen.h: dynamic_value.h
	bash ../../codegen/generate.sh $<

ip_addr.h.gen.c ip_addr.h.gen.h: ip_addr.h
	bash ../../codegen/generate.sh $<

../lib/stubs/ether_addr.h.gen.c ../lib/stubs/ether_addr.h.gen.h: ../lib/stubs/ether_addr.h
	bash ../../codegen/generate.sh $<

policer_loop.h policer_loop.c policer_state.c policer_state.h: policer_data_spec.ml
	bash ../../codegen/gen-loop-boilerplate.sh policer_data_spec.ml
