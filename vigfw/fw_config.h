#pragma once

#include <stdint.h>

#include <rte_ether.h>

#include "nf.h"
#include "libvig/nf_time.h"



struct nf_config {
  // WAN device, i.e. external
  uint16_t wan_device;

  // MAC addresses of devices
  struct ether_addr* device_macs;

  // MAC addresses of the endpoints the devices are linked to
  struct ether_addr* endpoint_macs;

  // Expiration time of flows in seconds
  vigor_time_t expiration_time;

  // Size of the flow table
  uint32_t max_flows;
};
