NF_FILES := policer_main.c policer_config.c

NF_AUTOGEN_SRCS := dynamic_value.h ip_addr.h

NF_ARGS := --wan 0 --lan 1 --rate $(or $(POLICER_RATE),375000000) --burst $(or $(POLICER_BURST),3750000000) --capacity $(or $(CAPACITY),65536)

NF_LAYER := 3

include $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/../Makefile
