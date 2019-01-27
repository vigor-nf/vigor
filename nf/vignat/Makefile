# Binary name
APP := nat

# Runtime and verification files
NF_FILES := nat_main.c nat_config.c \
            flow.h.gen.c nat_flowmanager.c

AUTO_GEN_FILES := flow.h.gen.c flow.h.gen.h

# Must generate the flow.h* files before building the app
all: $(AUTO_GEN_FILES) $(APP)

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

flow.h.gen.c flow.h.gen.h: flow.h
	bash ../../codegen/generate.sh flow.h
