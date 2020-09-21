#ifndef _ETHER_ADDR_H_INCLUDED_
#define _ETHER_ADDR_H_INCLUDED_

#include <stdbool.h>
#include <rte_ether.h>
#include "boilerplate-util.h"

/*@
  inductive rte_ether_addri = rte_ether_addrc(uint8_t , uint8_t , uint8_t , uint8_t , uint8_t , uint8_t );

  predicate rte_ether_addrp(struct rte_ether_addr* ptr; rte_ether_addri v) =
    struct_rte_ether_addr_padding(ptr) &*&
    uchars(ptr->addr_bytes, 6, ?addr_bytes_f) &*&
    length(addr_bytes_f) == 6 &*&
    addr_bytes_f == cons(?addr_bytes_0, cons(?addr_bytes_1, cons(?addr_bytes_2, cons(?addr_bytes_3, cons(?addr_bytes_4, cons(?addr_bytes_5, ?_nil)))))) &*&
    switch(_nil) { case nil: return true; case cons(nh, nt): return false; } &*&
    v == rte_ether_addrc(addr_bytes_0, addr_bytes_1, addr_bytes_2, addr_bytes_3, addr_bytes_4, addr_bytes_5);

  fixpoint unsigned _rte_ether_addr_hash(rte_ether_addri x) {
    switch(x) { case rte_ether_addrc(addr_bytes_0, addr_bytes_1, addr_bytes_2, addr_bytes_3, addr_bytes_4, addr_bytes_5):
      return crc32_hash(crc32_hash(crc32_hash(crc32_hash(crc32_hash(crc32_hash(0, addr_bytes_0), addr_bytes_1), addr_bytes_2), addr_bytes_3), addr_bytes_4), addr_bytes_5);
    }
  }
@*/

#define DEFAULT_RTE_ETHER_ADDR rte_ether_addrc(0, 0, 0, 0, 0, 0)

unsigned rte_ether_addr_hash(void* obj);
//@ requires [?f]rte_ether_addrp(obj, ?v);
//@ ensures [f]rte_ether_addrp(obj, v) &*& result == _rte_ether_addr_hash(v);

bool rte_ether_addr_eq(void* a, void* b);
//@ requires [?f1]rte_ether_addrp(a, ?aid) &*& [?f2]rte_ether_addrp(b, ?bid);
/*@ ensures [f1]rte_ether_addrp(a, aid) &*& [f2]rte_ether_addrp(b, bid) &*&
            (result ? aid == bid : aid != bid); @*/

void rte_ether_addr_allocate(void* obj);
//@ requires chars(obj, sizeof(struct rte_ether_addr), _);
//@ ensures rte_ether_addrp(obj, DEFAULT_RTE_ETHER_ADDR);


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
