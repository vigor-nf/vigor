#ifndef _PACKET_IO_H_INCLUDED_
#define _PACKET_IO_H_INCLUDED_

#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>
#include <rte_ether.h> //for sizeof(struct ether_hdr)

struct rte_mempool;

/*@

  fixpoint int borrowed_len(list<pair<int8_t*, int> > missing_chunks) {
    switch(missing_chunks) {
      case nil: return 0;
      case cons(h,t): return switch(h) { case pair(beginning, span):
        return span + borrowed_len(t);
      };
    }
  }
@*/

/*@
  predicate packetp(void* p,
                    list<int8_t> unread,
                    list<pair<int8_t*, int> > missing_chunks);
  @*/

// The main IO primitive.
void packet_borrow_next_chunk(void *p, size_t length, void **chunk);
/*@ requires packetp(p, ?unread, ?mc) &*&
             length <= length(unread) &*&
             0 < length &*& length < INT_MAX &*&
             length + borrowed_len(mc) < INT_MAX &*&
             *chunk |-> _; @*/
/*@ ensures *chunk |-> ?ptr &*&
            ptr != 0 &*&
            packetp(p, drop(length, unread), cons(pair(ptr, length), mc)) &*&
            chars(ptr, length, take(length, unread)); @*/

void packet_return_chunk(void *p, void *chunk);
/*@ requires packetp(p, ?unread, cons(pair(chunk, ?len), ?mc)) &*&
             chars(chunk, len, ?chnk); @*/
/*@ ensures packetp(p, append(chnk, unread), mc); @*/

uint32_t packet_get_unread_length(void *p);
/*@ requires packetp(p, ?unread, ?mc); @*/
/*@ ensures packetp(p, unread, mc) &*&
            result == length(unread); @*/

void packet_state_total_length(void *p, uint32_t *len);
/*@ requires packetp(p, ?unread, nil) &*&
             *len |-> length(unread); @*/
/*@ ensures packetp(p, unread, nil) &*&
            *len |-> length(unread); @*/

bool packet_receive(uint16_t src_device, void **p, uint32_t *len);
/*@ requires *p |-> _ &*& *len |-> ?length; @*/
/*@ ensures result ? *p |-> ?pp &*&
                     packetp(pp, ?unread, nil) &*&
                     sizeof(struct ether_hdr) <= length(unread) &*&
                     *len |-> length &*&
                     length == length(unread)
                   : *p |-> _ &*& *len |-> length; @*/

void packet_send(void *p, uint16_t dst_device);
/*@ requires packetp(p, _, nil); @*/
/*@ ensures true; @*/

void packet_free(void *p);
/*@ requires packetp(p, _, nil); @*/
/*@ ensures true; @*/

#endif // _PACKET_IO_H_INCLUDED_
