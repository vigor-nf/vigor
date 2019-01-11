#ifndef _PACKET_IO_H_INCLUDED_
#define  _PACKET_IO_H_INCLUDED_

#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>
#include <rte_ether.h>//for sizeof(struct ether_hdr)

struct Packet;
struct rte_mempool;

/*@
  predicate packetp(struct Packet* p, int nic, int type,
                    list<uint8_t> unread, list<pair<uint8_t*, int> > missing_chunks);
  @*/

// The main IO primitive.
void packet_borrow_next_chunk(struct Packet* p, size_t length, uint8_t** chunk);
/*@ requires packetp(p, ?nic, ?type, ?unread, ?mc) &*&
             length <= length(unread) &*&
             *chunk |-> _; @*/
/*@ ensures *chunk |-> ?ptr &*&
            packetp(p, nic, type, drop(length, unread), cons(pair(ptr, length), mc)) &*&
            uchars(ptr, length, take(length, unread)); @*/

void packet_return_chunk(struct Packet* p, uint8_t* chunk);
/*@ requires packetp(p, ?nic, ?type, ?unread, cons(pair(chunk, ?len), ?mc)) &*&
             uchars(chunk, len, ?chnk); @*/
/*@ ensures packetp(p, nic, type, append(chnk, unread), mc); @*/

bool packet_receive(uint16_t src_device, struct Packet** p);
/*@ requires *p |-> _; @*/
/*@ ensures result ? *p |-> ?pp &*&
                     packetp(pp, src_device, _, ?unread, nil) &*&
                     sizeof(struct ether_hdr) <= length(unread)
                   : *p |-> _; @*/

void packet_send(struct Packet* p, uint16_t dst_device);
/*@ requires packetp(p, _, _, _, nil); @*/
/*@ ensures true; @*/

// Flood method for the bridge
void packet_flood(struct Packet* p, uint16_t skip_device, uint16_t nb_devices,
                  struct rte_mempool* clone_pool);
/*@ requires packetp(p, _, _, _, nil); @*/
/*@ ensures true; @*/

void packet_free(struct Packet* p);
/*@ requires packetp(p, _, _, _, nil); @*/
/*@ ensures true; @*/

uint32_t packet_is_ipv4(struct Packet* p);
/*@ requires packetp(p, ?nic, ?type, ?unread, ?mc); @*/
/*@ ensures packetp(p, nic, type, unread, mc) &*&
            (result == 0 ?
              ((type & 0x10) != 0x10) :
              ((type & 0x10) == 0x10) &*& result == 1); @*/

uint16_t packet_get_port(struct Packet* p);
/*@ requires packetp(p, ?nic, ?type, ?unread, ?mc); @*/
/*@ ensures packetp(p, nic, type, unread, mc) &*&
            result == nic; @*/

uint32_t packet_get_unread_length(struct Packet* p);
/*@ requires packetp(p, ?nic, ?type, ?unread, ?mc); @*/
/*@ ensures packetp(p, nic, type, unread, mc) &*&
            result == length(unread); @*/

#endif// _PACKET_IO_H_INCLUDED_
