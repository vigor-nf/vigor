// DPDK requires these but doesn't include them. :|
#include <linux/limits.h>
#include <sys/types.h>
#include <unistd.h>

#include <stdlib.h>

#include <rte_common.h>
#include <rte_ip.h>
#include <rte_mbuf.h>

#include "flow.h.gen.h"
#include "nat_flowmanager.h"
#include "nat_config.h"
#include "lib/nf_forward.h"
#include "lib/nf_log.h"
#include "lib/nf_util.h"

struct nat_config config;
struct FlowManager* flow_manager;

void nf_core_init()
{
	flow_manager = flow_manager_allocate(
		config.start_port,
                config.external_addr,
                config.wan_device,
                config.expiration_time,
                config.max_flows
	);

	if (flow_manager == NULL) {
		rte_exit(EXIT_FAILURE, "Could not allocate flow manager");
	}
}

int nf_core_process(struct rte_mbuf* mbuf, vigor_time_t now)
{
  const int in_port = mbuf->port;
	NF_DEBUG("It is %" PRId64, now);

	flow_manager_expire(flow_manager, now);
	NF_DEBUG("Flows have been expired");

	struct ether_hdr* ether_header = nf_then_get_ether_header(mbuf_pkt(mbuf));

  if (!RTE_ETH_IS_IPV4_HDR(mbuf->packet_type)) {
		NF_DEBUG("Not IPv4, dropping");
		return in_port;
  }
  uint8_t* ip_options;
  bool wellformed = true;
	struct ipv4_hdr* ipv4_header = nf_then_get_ipv4_header(mbuf_pkt(mbuf), &ip_options, &wellformed);
  if (!wellformed) {
		NF_DEBUG("Malformed IPv4, dropping");
		return in_port;
  }
  assert(ipv4_header != NULL);

  if (!nf_has_tcpudp_header(ipv4_header) ||
      packet_get_unread_length(mbuf_pkt(mbuf)) < sizeof(struct tcpudp_hdr)) {
		NF_DEBUG("Not TCP/UDP, dropping");
		return in_port;
	}
	struct tcpudp_hdr* tcpudp_header = nf_then_get_tcpudp_header(mbuf_pkt(mbuf));
  assert(tcpudp_header != NULL);

	NF_DEBUG("Forwarding an IPv4 packet on device %" PRIu16, in_port);

	uint16_t dst_device;
	if (in_port == config.wan_device) {
		NF_DEBUG("Device %" PRIu16 " is external", in_port);

    struct FlowId internal_flow;
		if (flow_manager_get_external(flow_manager, tcpudp_header->dst_port, now, &internal_flow)) {
			NF_DEBUG("Found internal flow.");
      log_FlowId(&internal_flow);

      if (internal_flow.dst_ip != ipv4_header->src_addr ||
          internal_flow.dst_port != tcpudp_header->src_port ||
          internal_flow.protocol != ipv4_header->next_proto_id) {
        NF_DEBUG("Spoofing attempt, dropping.");
        return in_port;
      }

			ipv4_header->dst_addr = internal_flow.src_ip;
			tcpudp_header->dst_port = internal_flow.src_port;
			dst_device = internal_flow.internal_device;
		} else {
			NF_DEBUG("Unknown flow, dropping");
			return in_port;
		}
	} else {
    struct FlowId id = {
      .src_port = tcpudp_header->src_port,
      .dst_port = tcpudp_header->dst_port,
      .src_ip = ipv4_header->src_addr,
      .dst_ip = ipv4_header->dst_addr,
      .protocol = ipv4_header->next_proto_id,
      .internal_device = in_port
    };

    NF_DEBUG("For id:");
    log_FlowId(&id);

		NF_DEBUG("Device %" PRIu16 " is internal (not %" PRIu16 ")", in_port, config.wan_device);

    uint16_t external_port;
		if (!flow_manager_get_internal(flow_manager, &id, now, &external_port)) {
			NF_DEBUG("New flow");

			if (!flow_manager_allocate_flow(flow_manager, &id, in_port, now, &external_port)) {
				NF_DEBUG("No space for the flow, dropping");
				return in_port;
			}
		}

		NF_DEBUG("Forwarding from ext port:%d", external_port);

		ipv4_header->src_addr = config.external_addr;
		tcpudp_header->src_port = external_port;
		dst_device = config.wan_device;
	}

 	nf_set_ipv4_udptcp_checksum(ipv4_header, tcpudp_header, mbuf_pkt(mbuf));

  concretize_devices(&dst_device, rte_eth_dev_count());

	ether_header->s_addr = config.device_macs[dst_device];
	ether_header->d_addr = config.endpoint_macs[dst_device];

	return dst_device;
}


void nf_config_init(int argc, char** argv) {
  nat_config_init(&config, argc, argv);
}

void nf_config_cmdline_print_usage(void) {
  nat_config_cmdline_print_usage();
}

void nf_print_config() {
  nat_print_config(&config);
}
