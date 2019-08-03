# Runtime and verification files
NF_FILES := fw_main.c fw_config.c fw_flowmanager.c \

NF_AUTOGEN_SRCS := flow.h

# Verification arguments
NF_VERIF_ARGS := --wan 1 \
                 --expire 10 \
                 --max-flows 65536 \
                 --eth-dest 0,01:23:45:67:89:00 \
                 --eth-dest 1,01:23:45:67:89:01

# Include parent (in a convoluted way cause of DPDK)
include $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/../Makefile
