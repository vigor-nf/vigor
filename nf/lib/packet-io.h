#ifndef _PACKET_IO_H_INCLUDED_
#define  _PACKET_IO_H_INCLUDED_

#include <stdbool.h>
#include <stdint.h>
#include <assert.h>
#include <rte_byteorder.h>
#include <rte_common.h>
#include <rte_ether.h>
#include <rte_ethdev.h>
#include <rte_ip.h>
#include <rte_mbuf.h>
#include <rte_mbuf_ptype.h>

struct Packet;

// The main IO primitive.
char* packet_borrow_next_chunk(struct Packet* p, size_t length);
void packet_return_chunk(struct Packet* p, char* chunk);
bool packet_receive(uint16_t src_device, struct Packet** p);
void packet_send(struct Packet* p, uint16_t dst_device);
// Flood method for the bridge
void packet_flood(struct Packet* p, uint16_t skip_device, uint16_t nb_devices);
void packet_free(struct Packet* p);

bool packet_is_ipv4(struct Packet* p);

uint16_t packet_get_port(struct Packet* p);

#endif// _PACKET_IO_H_INCLUDED_
