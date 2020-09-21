#include <stdlib.h>

#include "flow.h.gen.h"
#include "fw_flowmanager.h"
#include "fw_config.h"
#include "nf.h"
#include "nf-log.h"
#include "nf-util.h"

struct nf_config config;

struct FlowManager *flow_manager;

bool nf_init(void) {
  flow_manager = flow_manager_allocate(
      config.wan_device, config.expiration_time, config.max_flows);
  return flow_manager != NULL;
}

int nf_process(uint16_t device, uint8_t* buffer, uint16_t packet_length, vigor_time_t now) {
  NF_DEBUG("It is %" PRId64, now);

  flow_manager_expire(flow_manager, now);
  NF_DEBUG("Flows have been expired");

  struct rte_ether_hdr *rte_ether_header = nf_then_get_rte_ether_header(buffer);
  uint8_t *ip_options;
  struct rte_ipv4_hdr *rte_ipv4_header =
      nf_then_get_rte_ipv4_header(rte_ether_header, buffer, &ip_options);
  if (rte_ipv4_header == NULL) {
    NF_DEBUG("Not IPv4, dropping");
    return device;
  }

  struct tcpudp_hdr *tcpudp_header =
      nf_then_get_tcpudp_header(rte_ipv4_header, buffer);
  if (tcpudp_header == NULL) {
    NF_DEBUG("Not TCP/UDP, dropping");
    return device;
  }

  NF_DEBUG("Forwarding an IPv4 packet on device %" PRIu16, device);

  uint16_t dst_device;
  if (device == config.wan_device) {
    // Inverse the src and dst for the "reply flow"
    struct FlowId id = {
      .src_port = tcpudp_header->dst_port,
      .dst_port = tcpudp_header->src_port,
      .src_ip = rte_ipv4_header->dst_addr,
      .dst_ip = rte_ipv4_header->src_addr,
      .protocol = rte_ipv4_header->next_proto_id,
    };

    uint32_t dst_device_long;
    if (!flow_manager_get_refresh_flow(flow_manager, &id, now,
                                       &dst_device_long)) {
      NF_DEBUG("Unknown external flow, dropping");
      return device;
    }
    dst_device = dst_device_long;
  } else {
    struct FlowId id = {
      .src_port = tcpudp_header->src_port,
      .dst_port = tcpudp_header->dst_port,
      .src_ip = rte_ipv4_header->src_addr,
      .dst_ip = rte_ipv4_header->dst_addr,
      .protocol = rte_ipv4_header->next_proto_id,
    };
    flow_manager_allocate_or_refresh_flow(flow_manager, &id, device, now);
    dst_device = config.wan_device;
  }

  concretize_devices(&dst_device, rte_eth_dev_count_avail());

  rte_ether_header->s_addr = config.device_macs[dst_device];
  rte_ether_header->d_addr = config.endpoint_macs[dst_device];

  return dst_device;
}
