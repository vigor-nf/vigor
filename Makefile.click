# Makefile for Click baseline NFs

CLICK_DIR := $(VIGOR_DIR)/fastclick
ifeq (true,$(VIGOR_USE_BATCH))
CLICK_DIR := $(VIGOR_DIR)/fastclick-batch
endif

compile:
	@echo 'No compile needed for Click NFs!'

run:
	@sudo $(CLICK_DIR)/bin/click --dpdk $(NF_DPDK_ARGS) -- nf.click
