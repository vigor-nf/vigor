# Binary name
APP := fw

# Runtime and verification files
NF_FILES := fw_main.c fw_config.c \
            flow.h.gen.c fw_flowmanager.c \
            fw_state.c

AUTO_GEN_FILES := flow.h.gen.c flow.h.gen.h ../lib/stubs/ether_addr.h.gen.h fw_loop.h fw_loop.c fw_state.h fw_state.c

# Must generate the flow.h* files before building the app
all: $(AUTO_GEN_FILES) $(APP)

# Verification files
NF_VERIF_FILES := fw_loop.c

# Verification arguments
NF_VERIF_ARGS := --wan 1 \
                 --expire 10 \
                 --max-flows 65536 \
                 --eth-dest 0,01:23:45:67:89:00 \
                 --eth-dest 1,01:23:45:67:89:01

# Include parent (in a convoluted way cause of DPDK)
include $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/../Makefile

flow.h.gen.c flow.h.gen.h: flow.h
	bash ../../codegen/generate.sh flow.h

../lib/stubs/ether_addr.h.gen.h: ../lib/stubs/ether_addr.h
	bash ../../codegen/generate.sh ../lib/stubs/ether_addr.h

fw_loop.h fw_loop.c fw_state.h fw_state.c: fw_data_spec.ml
	bash ../../codegen/gen-loop-boilerplate.sh fw_data_spec.ml
