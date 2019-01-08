#ifndef _PACKET_IO_H_INCLUDED_
#define  _PACKET_IO_H_INCLUDED_

#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>

struct Packet;
struct rte_mempool;

/*@
  predicate packetp(struct Packet* p, int nic, int type, list<char> unread, list<pair<char*, int> > missing_chunks);
  @*/

// The main IO primitive.
char* packet_borrow_next_chunk(struct Packet* p, size_t length);
/*@ requires packetp(p, ?nic, ?type, ?unread, ?mc) &*&
             length <= length(unread); @*/
/*@ ensures packetp(p, nic, type, drop(length, unread), cons(pair(result, length), mc)) &*&
            chars(result, length, take(length, unread)); @*/

void packet_return_chunk(struct Packet* p, char* chunk);
/*@ requires packetp(p, ?nic, ?type, ?unread, cons(pair(chunk, ?len), ?mc)) &*&
             chars(chunk, len, ?chnk); @*/
/*@ ensures packetp(p, nic, type, append(chnk, unread), mc); @*/

bool packet_receive(uint16_t src_device, struct Packet** p);
/*@ requires *p |-> _; @*/
/*@ ensures result ? *p |-> ?pp &*& packetp(pp, src_device, _, _, nil) : *p |-> _; @*/
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

bool packet_is_ipv4(struct Packet* p);
/*@ requires packetp(p, ?nic, ?type, ?unread, ?mc); @*/
/*@ ensures packetp(p, nic, type, unread, mc) &*&
            result == ((type & 0x10) == 0x10); @*/

uint16_t packet_get_port(struct Packet* p);
/*@ requires packetp(p, ?nic, ?type, ?unread, ?mc); @*/
/*@ ensures packetp(p, nic, type, unread, mc) &*&
            result == nic; @*/

#endif// _PACKET_IO_H_INCLUDED_
