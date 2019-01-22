#ifndef _PACKET_IO_H_INCLUDED_
#define  _PACKET_IO_H_INCLUDED_

#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>
#include <rte_ether.h>//for sizeof(struct ether_hdr)

struct rte_mempool;

/*@
  predicate packetp(void* p,
                    list<int8_t> unread,
                    list<pair<int8_t*, int> > missing_chunks);
  @*/

// The main IO primitive.
void packet_borrow_next_chunk(void* p, size_t length, void** chunk);
/*@ requires packetp(p, ?unread, ?mc) &*&
             length <= length(unread) &*&
             0 < length &*& length < INT_MAX &*&
             *chunk |-> _; @*/
/*@ ensures *chunk |-> ?ptr &*&
            packetp(p, drop(length, unread), cons(pair(ptr, length), mc)) &*&
            chars(ptr, length, take(length, unread)); @*/

void packet_return_chunk(void* p, void* chunk);
/*@ requires packetp(p, ?unread, cons(pair(chunk, ?len), ?mc)) &*&
             chars(chunk, len, ?chnk); @*/
/*@ ensures packetp(p, append(chnk, unread), mc); @*/

uint32_t packet_get_unread_length(void* p);
/*@ requires packetp(p, ?unread, ?mc); @*/
/*@ ensures packetp(p, unread, mc) &*&
            result == length(unread); @*/


bool packet_receive(uint16_t src_device, void** p, uint16_t* len);
/*@ requires *p |-> _; @*/
/*@ ensures result ? *p |-> ?pp &*&
                     packetp(pp, ?unread, nil) &*&
                     sizeof(struct ether_hdr) <= length(unread)
                   : *p |-> _; @*/

void packet_send(void* p, uint16_t dst_device);
/*@ requires packetp(p, _, nil); @*/
/*@ ensures true; @*/

// Flood method for the bridge
void packet_flood(void* p, uint16_t skip_device, uint16_t nb_devices);
/*@ requires packetp(p, _, nil); @*/
/*@ ensures true; @*/

void packet_free(void* p);
/*@ requires packetp(p, _, nil); @*/
/*@ ensures true; @*/

void packet_clone(void* src, void** clone);
/*@ requires packetp(src, ?unread, ?mc) &*& *clone |-> _; @*/
/*@ ensures packetp(src, unread, mc) &*&
            *clone |-> ?p &*& packetp(p, unread, mc); @*/

#endif// _PACKET_IO_H_INCLUDED_
