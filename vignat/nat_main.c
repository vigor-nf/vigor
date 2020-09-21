#include <stdlib.h>

#include "nf.h"
#include "flow.h.gen.h"
#include "nat_flowmanager.h"
#include "nat_config.h"
#include "nf-log.h"
#include "nf-util.h"

struct nf_config config;

struct FlowManager *flow_manager;

bool nf_init(void) {
  flow_manager = flow_manager_allocate(
      config.start_port, config.external_addr, config.wan_device,
      config.expiration_time, config.max_flows);

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
    NF_DEBUG("Device %" PRIu16 " is external", device);

    struct FlowId internal_flow;
    if (flow_manager_get_external(flow_manager, tcpudp_header->dst_port, now,
                                  &internal_flow)) {
      NF_DEBUG("Found internal flow.");
      LOG_FLOWID(&internal_flow, NF_DEBUG);

      if (internal_flow.dst_ip != rte_ipv4_header->src_addr |
          internal_flow.dst_port != tcpudp_header->src_port |
          internal_flow.protocol != rte_ipv4_header->next_proto_id) {
        NF_DEBUG("Spoofing attempt, dropping.");
        return device;
      }

      rte_ipv4_header->dst_addr = internal_flow.src_ip;
      tcpudp_header->dst_port = internal_flow.src_port;
      dst_device = internal_flow.internal_device;
    } else {
      NF_DEBUG("Unknown flow, dropping");
      return device;
    }
  } else {
    struct FlowId id = { .src_port = tcpudp_header->src_port,
                         .dst_port = tcpudp_header->dst_port,
                         .src_ip = rte_ipv4_header->src_addr,
                         .dst_ip = rte_ipv4_header->dst_addr,
                         .protocol = rte_ipv4_header->next_proto_id,
                         .internal_device = device };

    NF_DEBUG("For id:");
    LOG_FLOWID(&id, NF_DEBUG);

    NF_DEBUG("Device %" PRIu16 " is internal (not %" PRIu16 ")", device,
             config.wan_device);

    uint16_t external_port;
    if (!flow_manager_get_internal(flow_manager, &id, now, &external_port)) {
      NF_DEBUG("New flow");

      if (!flow_manager_allocate_flow(flow_manager, &id, device, now,
                                      &external_port)) {
        NF_DEBUG("No space for the flow, dropping");
        return device;
      }
    }

    NF_DEBUG("Forwarding from ext port:%d", external_port);

    rte_ipv4_header->src_addr = config.external_addr;
    tcpudp_header->src_port = external_port;
    dst_device = config.wan_device;
  }

  nf_set_rte_ipv4_udptcp_checksum(rte_ipv4_header, tcpudp_header, buffer);

  concretize_devices(&dst_device, rte_eth_dev_count_avail());

  rte_ether_header->s_addr = config.device_macs[dst_device];
  rte_ether_header->d_addr = config.endpoint_macs[dst_device];

  return dst_device;
}
