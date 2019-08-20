NF_PROCESS_NAME := libmoon

NF_LAYER := 3

MOONPOL_ARGS := -b 1
ifeq (true,$(VIGOR_USE_BATCH))
MOONPOL_ARGS := -b 32
endif

# for substitutions into dpdk-conf.lua in run:
dquote := "
space := $(null) #
comma := ,

compile:
	@echo 'No compile needed!'

run:
	@rm -f /tmp/dpdk-conf.lua
	@if [ '$(NF_DPDK_ARGS)' != '' ]; \
	  then echo 'DPDKConfig { cli = { "$(subst $(space),$(dquote)$(comma)$(dquote),$(NF_DPDK_ARGS))" } }' \
	            > /tmp/dpdk-conf.lua; \
	 fi
	@# OK if the file doesn't exist, libmoon just ignores it
	@sudo $(VIGOR_DIR)/libmoon/build/libmoon policer.lua \
	                                         --dpdk-config=/tmp/dpdk-conf.lua \
	                                         $(MOONPOL_ARGS)


include $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/../Makefile
