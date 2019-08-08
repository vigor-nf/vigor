# Makefile for Click baseline NFs

CLICK_DIR := $(VIGOR_DIR)/fastclick

compile:
	@echo 'No compile needed!'

run:
	@sudo $(CLICK_DIR)/bin/click --dpdk $(NF_DPDK_ARGS) -- nf.click
