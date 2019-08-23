#include <stdlib.h>
#include <assert.h>
#include <rte_ip.h>
#include <rte_mbuf.h>

#include "packet-io.h"

size_t global_total_length;
size_t global_read_length = 0;

/*@
  fixpoint bool missing_chunks(list<pair<int8_t*, int> > missing_chunks, int8_t*
                               start, int8_t* end) {
    switch(missing_chunks) { case nil: return start == end;
      case cons(h,t): return switch(h) { case pair(beginning, span):
        return start <= beginning && beginning <= end &&
               0 < span && span < INT_MAX &&
               0 <= (int8_t*)beginning - (int8_t*)start &&
               (int8_t*)beginning - (int8_t*)start < INT_MAX &&
               end == beginning + span && missing_chunks(t, start, beginning);
      };
    }
  }


  predicate packetp(void* p, list<int8_t> unread,
                    list<pair<int8_t*, int> > missing_chunks) =
    global_read_length |-> borrowed_len(missing_chunks) &*&
    global_total_length |-> borrowed_len(missing_chunks) + length(unread) &*&
    0 <= borrowed_len(missing_chunks) &*&
    (int8_t*)0 <= (int8_t*)p + borrowed_len(missing_chunks) &*&
    (int8_t*)p + borrowed_len(missing_chunks) + length(unread) <=
    (int8_t*)UINTPTR_MAX &*&
    (int8_t*)0 < p &*&
    true == missing_chunks(missing_chunks, p,
                           (int8_t*)p + borrowed_len(missing_chunks)) &*&
    chars((int8_t*)p + borrowed_len(missing_chunks), length(unread), unread);
  @*/

void packet_state_total_length(void *p, uint32_t *len)
/*@ requires packetp(p, ?unread, nil) &*&
             *len |-> length(unread); @*/
/*@ ensures packetp(p, unread, nil) &*&
            *len |-> length(unread); @*/
{
  //@ open packetp(p, unread, nil);
  // IGNORE(p);
  global_total_length = *len;
  //@ close packetp(p, unread, nil);
}

/*@
  lemma void borrowed_len_nonneg(list<pair<int8_t*, int> > missing_chunks,
                                 int8_t* start, int8_t* beginning)
  requires true == missing_chunks(missing_chunks, start, beginning);
  ensures 0 <= borrowed_len(missing_chunks);
  {
    switch(missing_chunks) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(beg, span):
          borrowed_len_nonneg(t, start, beg);
        }
    }
  }
@*/

// The main IO primitive.
void packet_borrow_next_chunk(void *p, size_t length, void **chunk)
/*@ requires packetp(p, ?unread, ?mc) &*&
             length <= length(unread) &*&
             0 < length &*& length < INT_MAX &*&
             length + borrowed_len(mc) < INT_MAX &*&
             *chunk |-> _; @*/
/*@ ensures *chunk |-> ?ptr &*&
            ptr != 0 &*&
            packetp(p, drop(length, unread), cons(pair(ptr, length), mc)) &*&
            chars(ptr, length, take(length, unread)); @*/
{
  //@ open packetp(p, unread, mc);
  //@ borrowed_len_nonneg(mc, p, p + borrowed_len(mc));
  //@ assert 0 <= global_read_length;
  //@ assert p > 0;
  //@ assert p + global_read_length > 0;
  // TODO: support mbuf chains.
  *chunk = (char *)p + global_read_length;
  //@ chars_split(*chunk, length);
  global_read_length += length;
  //@ assert *chunk |-> ?ptr;
  //@ close packetp(p, drop(length, unread), cons(pair(ptr, length), mc));
}

void packet_return_chunk(void *p, void *chunk)
/*@ requires packetp(p, ?unread, cons(pair(chunk, ?len), ?mc)) &*&
             chars(chunk, len, ?chnk); @*/
/*@ ensures packetp(p, append(chnk, unread), mc); @*/
{
  //@ open packetp(p, unread, cons(pair(chunk, len), mc));
  global_read_length = (uint32_t)((int8_t *)chunk - (int8_t *)p);
  //@ close packetp(p, append(chnk, unread), mc);
}

uint32_t packet_get_unread_length(void *p)
/*@ requires packetp(p, ?unread, ?mc); @*/
/*@ ensures packetp(p, unread, mc) &*&
            result == length(unread); @*/
{
  //@ open packetp(p, unread, mc);
  return global_total_length - global_read_length;
  //@ close packetp(p, unread, mc);
}
