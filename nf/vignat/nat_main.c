// DPDK requires these but doesn't include them. :|
#include <linux/limits.h>
#include <sys/types.h>
#include <unistd.h>

#include <stdlib.h>

#include <rte_common.h>
#include <rte_ip.h>
#include <rte_mbuf.h>

#include "nat_flow.h"
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

int nf_core_process(struct rte_mbuf* mbuf, time_t now)
{
	NF_DEBUG("It is %" PRId64, now);

	flow_manager_expire(flow_manager, now);
	NF_DEBUG("Flows have been expired");

	struct ether_hdr* ether_header = nf_get_mbuf_ether_header(mbuf);

	struct ipv4_hdr* ipv4_header = nf_get_mbuf_ipv4_header(mbuf);
	if (ipv4_header == NULL) {
		NF_DEBUG("Not IPv4, dropping");
		return mbuf->port;
	}

	struct tcpudp_hdr* tcpudp_header = nf_get_ipv4_tcpudp_header(ipv4_header);
	if (tcpudp_header == NULL) {
		NF_DEBUG("Not TCP/UDP, dropping");
		return mbuf->port;
	}

	NF_DEBUG("Forwarding an IPv4 packet on device %" PRIu16, mbuf->port);

	uint16_t dst_device;
	if (mbuf->port == config.wan_device) {
		NF_DEBUG("Device %" PRIu16 " is external", mbuf->port);

    struct FlowId internal_flow;
		if (flow_manager_get_external(flow_manager, tcpudp_header->dst_port, now, &internal_flow)) {
			NF_DEBUG("Found internal flow.");
      flow_log_id(&internal_flow);

			ipv4_header->dst_addr = internal_flow.src_ip;
			tcpudp_header->dst_port = internal_flow.src_port;
			dst_device = internal_flow.internal_device;
		} else {
			NF_DEBUG("Unknown flow, dropping");
			return mbuf->port;
		}
	} else {
    struct FlowId id = {
      .src_port = tcpudp_header->src_port,
      .dst_port = tcpudp_header->dst_port,
      .src_ip = ipv4_header->src_addr,
      .dst_ip = ipv4_header->dst_addr,
      .protocol = ipv4_header->next_proto_id,
      .internal_device = mbuf->port
    };

    NF_DEBUG("For id:");
    flow_log_id(&id);

		NF_DEBUG("Device %" PRIu16 " is internal (not %" PRIu16 ")", mbuf->port, config.wan_device);

    uint16_t external_port;
		if (!flow_manager_get_internal(flow_manager, &id, now, &external_port)) {
			NF_DEBUG("New flow");

			if (!flow_manager_allocate_flow(flow_manager, &id, mbuf->port, now, &external_port)) {
				NF_DEBUG("No space for the flow, dropping");
				return mbuf->port;
			}
		}

		NF_DEBUG("Forwarding from ext port:%d", external_port);

		ipv4_header->src_addr = config.external_addr;
		tcpudp_header->src_port = external_port;
		dst_device = config.wan_device;
	}

	ether_header->s_addr = config.device_macs[dst_device];
	ether_header->d_addr = config.endpoint_macs[dst_device];
	nf_set_ipv4_checksum(ipv4_header);

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

#ifdef KLEE_VERIFICATION
#include "nat_loop.h"

void nf_loop_iteration_begin(unsigned lcore_id,
                             time_t time) {
  loop_iteration_begin(flow_manager_get_in_table(flow_manager),
                       flow_manager_get_in_vec(flow_manager),
                       flow_manager_get_chain(flow_manager),
                       lcore_id, time,
                       config.max_flows,
                       config.start_port);
}

void nf_add_loop_iteration_assumptions(unsigned lcore_id,
                                       time_t time) {
  loop_iteration_assumptions(flow_manager_get_in_table(flow_manager),
                             flow_manager_get_in_vec(flow_manager),
                             flow_manager_get_chain(flow_manager),
                             lcore_id, time,
                             config.max_flows,
                             config.start_port);
}

void nf_loop_iteration_end(unsigned lcore_id,
                           time_t time) {
  loop_iteration_end(flow_manager_get_in_table(flow_manager),
                     flow_manager_get_in_vec(flow_manager),
                     flow_manager_get_chain(flow_manager),
                     lcore_id, time,
                     config.max_flows,
                     config.start_port);
}
#endif

