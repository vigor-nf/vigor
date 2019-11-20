NF_FILES := nat_main.c nat_config.c nat_flowmanager.c

NF_AUTOGEN_SRCS := flow.h

NF_ARGS := --wan 1 \
           --expire $(or $(EXPIRATION_TIME),10) \
           --starting-port 0 \
           --max-flows $(or $(CAPACITY),65536) \
           --extip $(or $(MB_IP_EXTERNAL),0.0.0.0) \
           --eth-dest 0,$(or $(TESTER_MAC_EXTERNAL),01:23:45:67:89:00) \
           --eth-dest 1,$(or $(TESTER_MAC_INTERNAL),01:23:45:67:89:01)

NF_LAYER := 4


include $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/../Makefile
