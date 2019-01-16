#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

#include <netinet/in.h>

#include <rte_byteorder.h>
#include <rte_common.h>
#include <rte_ether.h>
#include <rte_ip.h>
#include <rte_mbuf.h>
#include <rte_mbuf_ptype.h>
#include <rte_tcp.h>
#include <rte_udp.h>

#include "nf_util.h"

void* chunks_borrowed[MAX_N_CHUNKS];
size_t chunks_borrowed_num = 0;

bool
nf_has_tcpudp_header(struct ipv4_hdr* header)
{
  return header->next_proto_id == IPPROTO_TCP || header->next_proto_id == IPPROTO_UDP;
}

void
nf_set_ipv4_checksum(struct ipv4_hdr* header)
{
	// TODO: See if can be offloaded to hardware
	header->hdr_checksum = 0;

	if (header->next_proto_id == IPPROTO_TCP) {
		struct tcp_hdr* tcp_header = (struct tcp_hdr*)(header + 1);
		tcp_header->cksum = 0;
		tcp_header->cksum = rte_ipv4_udptcp_cksum(header, tcp_header);
	} else if (header->next_proto_id == IPPROTO_UDP) {
		struct udp_hdr * udp_header = (struct udp_hdr*)(header + 1);
		udp_header->dgram_cksum = 0;
		udp_header->dgram_cksum = rte_ipv4_udptcp_cksum(header, udp_header);
	}

  // FIXME: this is misleading. we don't really compute any checksum here,
  // see rte_ipv4_udptcp_cksum and rte_ipv4_udptcp_cksum, they return 0!
	header->hdr_checksum = rte_ipv4_cksum(header);
}

uintmax_t
nf_util_parse_int(const char* str, const char* name,
                  int base, char next) {
  char* temp;
  intmax_t result = strtoimax(str, &temp, base);

  // There's also a weird failure case with overflows, but let's not care
  if(temp == str || *temp != next) {
    rte_exit(EXIT_FAILURE, "Error while parsing '%s': %s\n", name, str);
  }

  return result;
}

char*
nf_mac_to_str(struct ether_addr* addr)
{
	// format is xx:xx:xx:xx:xx:xx\0
	uint16_t buffer_size = 6 * 2 + 5 + 1; //FIXME: why dynamic alloc here?
	char* buffer = (char*) calloc(buffer_size, sizeof(char));
	if (buffer == NULL) {
		rte_exit(EXIT_FAILURE, "Out of memory in nf_mac_to_str!");
	}

	ether_format_addr(buffer, buffer_size, addr);
	return buffer;
}

char*
nf_ipv4_to_str(uint32_t addr)
{
	// format is xxx.xxx.xxx.xxx\0
	uint16_t buffer_size = 4 * 3 + 3 + 1;
	char* buffer = (char*) calloc(buffer_size, sizeof(char)); //FIXME: why dynamic alloc here?
	if (buffer == NULL) {
		rte_exit(EXIT_FAILURE, "Out of memory in nf_ipv4_to_str!");
	}

	snprintf(buffer, buffer_size, "%" PRIu8 ".%" PRIu8 ".%" PRIu8 ".%" PRIu8,
		 addr        & 0xFF,
		(addr >>  8) & 0xFF,
		(addr >> 16) & 0xFF,
		(addr >> 24) & 0xFF
	);
	return buffer;
}
