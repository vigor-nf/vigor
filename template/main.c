#include "nf.h"
#include "config.h"

#include <rte_common.h>

#include "libvig/nf_log.h"
#include "libvig/nf_util.h"


// ===
// Include the state, and the generated structures, like so:
// ===
#include "state.h"
#include "flow.h.gen.h"


void nf_init(void)
{
	// ===
	// Initialize your NF here, e.g. non-configuration global variables
	// You must at least allocate the state.
	// ===
	if (alloc_state(42) == NULL) {
		rte_exit(EXIT_FAILURE, "Not enough memory for state");
	}
}

int nf_process(struct rte_mbuf* mbuf, vigor_time_t now)
{
	// ===
	// Process the packet here, and return either the port on which the packet should be forwarded, or:
	// - the input port, to drop the packet, or
	// - FLOOD_FRAME, to send the packet to all ports except the input one.
	//
	// You can access the port the mbuf came from with mbuf->port,
	//
	// You can access the configuration using the 'config' global variable, as declared in nf.h.
	//
	// This example simply reads the L2/L3/L4 headers, changes the L2 addresses, then forwards to the "other" port, assuming there are 2.
	// ===

	struct ether_hdr* ether_header = nf_then_get_ether_header(mbuf_pkt(mbuf));
	if (mbuf->packet_type != 0 && !RTE_ETH_IS_IPV4_HDR(mbuf->packet_type)) {
		NF_DEBUG("Not IPv4, dropping");
		return mbuf->port;
	}
	uint8_t* ip_options;
	bool wellformed = true;
	struct ipv4_hdr* ipv4_header = nf_then_get_ipv4_header(mbuf_pkt(mbuf), &ip_options, &wellformed);
	if (!wellformed) {
		NF_DEBUG("Malformed IPv4, dropping");
		return mbuf->port;
	}

	if (!nf_has_tcpudp_header(ipv4_header) || packet_get_unread_length(mbuf_pkt(mbuf)) < sizeof(struct tcpudp_hdr)) {
		NF_DEBUG("Not TCP/UDP, dropping");
		return mbuf->port;
	}
	struct tcpudp_hdr* tcpudp_header = nf_then_get_tcpudp_header(mbuf_pkt(mbuf));
	// You could do something with the headers here...
	// ...which would probably require you to recompute the checksums
 	nf_set_ipv4_udptcp_checksum(ipv4_header, tcpudp_header, mbuf_pkt(mbuf));

	uint16_t dst_device = 1 - mbuf->port;

	// Special method required during symbolic execution to avoid path explosion
	concretize_devices(&dst_device, rte_eth_dev_count());

	ether_header->s_addr = config->device_macs[dst_device];
	ether_header->d_addr = config->endpoint_macs[dst_device];

	return 1 - mbuf->port;
}
