NF_FILES := bridge_main.c bridge_config.c

NF_AUTOGEN_SRCS := dyn_value.h stat_key.h

NF_ARGS := --expire $(or $(EXPIRATION_TIME),10) --capacity $(or $(CAPACITY),65536)

include $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/../Makefile
