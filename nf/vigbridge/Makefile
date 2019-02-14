# Binary name
APP := bridge

# Runtime and verification files
NF_FILES := bridge_main.c bridge_config.c stat_key.h.gen.c dyn_value.h.gen.c ../lib/stubs/ether_addr.h.gen.c

# Verification files
NF_VERIF_FILES := bridge_loop.c

# Verification arguments
NF_VERIF_ARGS := --expire 10 --capacity 100 --config no-file.cfg

AUTO_GEN_FILES := dyn_value.h.gen.c dyn_value.h.gen.h \
                  stat_key.h.gen.c stat_key.h.gen.h \
                  ../lib/stubs/ether_addr.h.gen.c ../lib/stubs/ether_addr.h.gen.h \
                  bridge_loop.c bridge_loop.h

all: $(AUTO_GEN_FILES) $(APP)

# Include parent (in a convoluted way cause of DPDK)
include $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/../Makefile

dyn_value.h.gen.c dyn_value.h.gen.h: dyn_value.h
	bash ../../codegen/generate.sh dyn_value.h

stat_key.h.gen.c stat_key.h.gen.h ../lib/stubs/ether_addr.h.gen.c ../lib/stubs/ether_addr.h.gen.h: stat_key.h ../lib/stubs/ether_addr.h
	bash ../../codegen/generate.sh stat_key.h

bridge_loop.h bridge_loop.c: bridge_data_spec.ml
	bash ../../codegen/gen-loop-boilerplate.sh bridge_data_spec.ml
