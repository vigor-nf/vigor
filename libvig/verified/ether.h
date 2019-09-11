#ifndef _ETHER_ADDR_H_INCLUDED_
#define _ETHER_ADDR_H_INCLUDED_

#include <stdbool.h>
#include <rte_ether.h>
#include "boilerplate-util.h"

/*@
  inductive ether_addri = ether_addrc(uint8_t , uint8_t , uint8_t , uint8_t , uint8_t , uint8_t );

  predicate ether_addrp(struct ether_addr* ptr; ether_addri v) =
    struct_ether_addr_padding(ptr) &*&
    uchars(ptr->addr_bytes, 6, ?addr_bytes_f) &*&
    length(addr_bytes_f) == 6 &*&
    addr_bytes_f == cons(?addr_bytes_0, cons(?addr_bytes_1, cons(?addr_bytes_2, cons(?addr_bytes_3, cons(?addr_bytes_4, cons(?addr_bytes_5, ?_nil)))))) &*&
    switch(_nil) { case nil: return true; case cons(nh, nt): return false; } &*&
    v == ether_addrc(addr_bytes_0, addr_bytes_1, addr_bytes_2, addr_bytes_3, addr_bytes_4, addr_bytes_5);

  fixpoint unsigned _ether_addr_hash(ether_addri x) {
    switch(x) { case ether_addrc(addr_bytes_0, addr_bytes_1, addr_bytes_2, addr_bytes_3, addr_bytes_4, addr_bytes_5):
      return crc32_hash(crc32_hash(crc32_hash(crc32_hash(crc32_hash(crc32_hash(0, addr_bytes_0), addr_bytes_1), addr_bytes_2), addr_bytes_3), addr_bytes_4), addr_bytes_5);
    }
  }
@*/

#define DEFAULT_ETHER_ADDR ether_addrc(0, 0, 0, 0, 0, 0)

unsigned ether_addr_hash(void* obj);
//@ requires [?f]ether_addrp(obj, ?v);
//@ ensures [f]ether_addrp(obj, v) &*& result == _ether_addr_hash(v);

bool ether_addr_eq(void* a, void* b);
//@ requires [?f1]ether_addrp(a, ?aid) &*& [?f2]ether_addrp(b, ?bid);
/*@ ensures [f1]ether_addrp(a, aid) &*& [f2]ether_addrp(b, bid) &*&
            (result ? aid == bid : aid != bid); @*/

void ether_addr_allocate(void* obj);
//@ requires chars(obj, sizeof(struct ether_addr), _);
//@ ensures ether_addrp(obj, DEFAULT_ETHER_ADDR);


#define LOG_ETHER_ADDR(obj, p) \
  p("{"); \
  p("addr_bytes[0]: %d", (obj)->addr_bytes[0]); \
  p("addr_bytes[1]: %d", (obj)->addr_bytes[1]); \
  p("addr_bytes[2]: %d", (obj)->addr_bytes[2]); \
  p("addr_bytes[3]: %d", (obj)->addr_bytes[3]); \
  p("addr_bytes[4]: %d", (obj)->addr_bytes[4]); \
  p("addr_bytes[5]: %d", (obj)->addr_bytes[5]); \
  p("}");

#endif //_ETHER_ADDR_H_INCLUDED_
