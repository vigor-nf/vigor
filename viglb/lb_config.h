#pragma once

#include <inttypes.h>

#include <rte_ether.h>
#include "nf.h"

struct nf_config {
  // Number of backends
  uint16_t backend_count;

  // MAC addresses of the devices the backends are connected to
  struct rte_ether_addr *device_macs;

  // Size of the flow table
  uint32_t flow_capacity;

  // Expiration time of flows in microseconds
  uint32_t flow_expiration_time;

  // The maximum number of backends we can ballance at the same time
  uint32_t backend_capacity;

  // The height of the consistent hashing table.
  // Bigger value induces more memory usage, but can achieve finer
  // granularity.
  uint32_t cht_height;

  // The time in microseconds for which the load balancer is willing to wait
  // hoping to get another heartbeat. If no heartbeat comes for a host for this
  // time, it is considered down and removed from the pool of backends.
  uint32_t backend_expiration_time;

  // WAN device, i.e. external
  uint16_t wan_device;
};
