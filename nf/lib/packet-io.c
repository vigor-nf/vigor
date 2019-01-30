#include <stdlib.h>
#include <assert.h>
#include <rte_ip.h>
#include <rte_mbuf.h>

#include "packet-io.h"

size_t global_total_length;
size_t global_read_length = 0;

/*@
  fixpoint bool missing_chunks(list<pair<int8_t*, int> > missing_chunks, int8_t* start, int8_t* end) {
    switch(missing_chunks) {
      case nil: return start == end;
      case cons(h,t): return switch(h) { case pair(beginning, span):
        return start <= beginning && beginning <= end &&
               0 < span && span < INT_MAX &&
               end == beginning + span && missing_chunks(t, start, beginning);
      };
    }
  }

  fixpoint int borrowed_len(list<pair<int8_t*, int> > missing_chunks) {
    switch(missing_chunks) {
      case nil: return 0;
      case cons(h,t): return switch(h) { case pair(beginning, span):
        return span + borrowed_len(t);
      };
    }
  }

  predicate packetp(void* p, list<int8_t> unread, list<pair<int8_t*, int> > missing_chunks) =
    global_unread_buf |-> ?unread_buf &*&
    global_read_length |-> borrowed_len(missing_chunks) &*&
    global_total_length |-> borrowed_len(missing_chunks) + length(unread) &*&
    p <= unread_buf &*& unread_buf <= p + borrowed_len(missing_chunks) + length(unread) &*&
    (int8_t*)p + borrowed_len(missing_chunks) + length(unread) <= (int8_t*)UINTPTR_MAX &*&
    (int8_t*)p + borrowed_len(missing_chunks) == (char*)(void*)unread_buf &*&
    true == missing_chunks(missing_chunks, p, unread_buf) &*&
    chars(unread_buf, length(unread), unread);
  @*/

// The main IO primitive.
void packet_borrow_next_chunk(void* p, size_t length, void** chunk)
/*@ requires packetp(p, ?unread, ?mc) &*&
             length <= length(unread) &*&
             0 < length &*& length < INT_MAX &*&
             *chunk |-> _; @*/
/*@ ensures *chunk |-> ?ptr &*&
            packetp(p, drop(length, unread), cons(pair(ptr, length), mc)) &*&
            chars(ptr, length, take(length, unread)); @*/
{
  //TODO: support mbuf chains.
  *chunk = (char*)p + global_read_length;
  global_read_length += length;
  global_total_length = length;
}

void packet_return_chunk(void* p, void* chunk)
/*@ requires packetp(p, ?unread, cons(pair(chunk, ?len), ?mc)) &*&
             chars(chunk, len, ?chnk); @*/
/*@ ensures packetp(p, append(chnk, unread), mc); @*/
{
  global_read_length = (int8_t*)chunk - (int8_t*)p;
}

uint32_t packet_get_unread_length(void* p)
/*@ requires packetp(p, ?unread, ?mc); @*/
/*@ ensures packetp(p, unread, mc) &*&
            result == length(unread); @*/
{
  //@ open packetp(p, unread, mc);
  return global_total_length - global_read_length;
  //@ close packetp(p, unread, mc);
}

