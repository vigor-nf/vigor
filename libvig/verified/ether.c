#include "libvig/verified/ether.h"

bool rte_ether_addr_eq(void* a, void* b)
//@ requires [?f1]rte_ether_addrp(a, ?aid) &*& [?f2]rte_ether_addrp(b, ?bid);
/*@ ensures [f1]rte_ether_addrp(a, aid) &*& [f2]rte_ether_addrp(b, bid) &*&
            (result ? aid == bid : aid != bid); @*/
{
  struct rte_ether_addr* id1 = (struct rte_ether_addr*) a;
  struct rte_ether_addr* id2 = (struct rte_ether_addr*) b;
  //@ open [f1]rte_ether_addrp(a, aid);
  //@ open [f2]rte_ether_addrp(b, bid);
  return (id1->addr_bytes[0] == id2->addr_bytes[0])
     AND (id1->addr_bytes[1] == id2->addr_bytes[1])
     AND (id1->addr_bytes[2] == id2->addr_bytes[2])
     AND (id1->addr_bytes[3] == id2->addr_bytes[3])
     AND (id1->addr_bytes[4] == id2->addr_bytes[4])
     AND (id1->addr_bytes[5] == id2->addr_bytes[5]);
  //@ close [f1]rte_ether_addrp(a, aid);
  //@ close [f2]rte_ether_addrp(b, bid);

}


void rte_ether_addr_allocate(void* obj)
//@ requires chars(obj, sizeof(struct rte_ether_addr), _);
//@ ensures rte_ether_addrp(obj, DEFAULT_RTE_ETHER_ADDR);
{

  struct rte_ether_addr* id = (struct rte_ether_addr*) obj;
  //@ close_struct((struct rte_ether_addr*) obj);
  //@ assert id->addr_bytes[0..6] |-> ?addr_bytes_lst;
  /*@   switch(addr_bytes_lst) { case cons(h0, t0):
    switch(t0) { case cons(h1, t1):
    switch(t1) { case cons(h2, t2):
    switch(t2) { case cons(h3, t3):
    switch(t3) { case cons(h4, t4):
    switch(t4) { case cons(h5, t5):

    case nil: assert false;
    }
    case nil: assert false;
    }
    case nil: assert false;
    }
    case nil: assert false;
    }
    case nil: assert false;
    }
    case nil: assert false;
    }@*/
  id->addr_bytes[0] = 0;
  id->addr_bytes[1] = 0;
  id->addr_bytes[2] = 0;
  id->addr_bytes[3] = 0;
  id->addr_bytes[4] = 0;
  id->addr_bytes[5] = 0;
  //@ close rte_ether_addrp(obj, DEFAULT_RTE_ETHER_ADDR);
}

#ifndef KLEE_VERIFICATION
unsigned rte_ether_addr_hash(void* obj)
//@ requires [?f]rte_ether_addrp(obj, ?v);
//@ ensures [f]rte_ether_addrp(obj, v) &*& result == _rte_ether_addr_hash(v);
{
  struct rte_ether_addr* id = (struct rte_ether_addr*) obj;

  //@ open [f]rte_ether_addrp(obj, v);
  uint8_t addr_bytes_0 = id->addr_bytes[0];
  //@ produce_limits(addr_bytes_0);
  uint8_t addr_bytes_1 = id->addr_bytes[1];
  //@ produce_limits(addr_bytes_1);
  uint8_t addr_bytes_2 = id->addr_bytes[2];
  //@ produce_limits(addr_bytes_2);
  uint8_t addr_bytes_3 = id->addr_bytes[3];
  //@ produce_limits(addr_bytes_3);
  uint8_t addr_bytes_4 = id->addr_bytes[4];
  //@ produce_limits(addr_bytes_4);
  uint8_t addr_bytes_5 = id->addr_bytes[5];
  //@ produce_limits(addr_bytes_5);
  //@ close [f]rte_ether_addrp(obj, v);

  unsigned hash = 0;
  hash = __builtin_ia32_crc32si(hash, addr_bytes_0);
  hash = __builtin_ia32_crc32si(hash, addr_bytes_1);
  hash = __builtin_ia32_crc32si(hash, addr_bytes_2);
  hash = __builtin_ia32_crc32si(hash, addr_bytes_3);
  hash = __builtin_ia32_crc32si(hash, addr_bytes_4);
  hash = __builtin_ia32_crc32si(hash, addr_bytes_5);
  return hash;
}
#endif// KLEE_VERIFICATION
