#include "policer_data.h"

#include <limits.h>


// Required for VeriFast to not complain about underflows
static uint64_t wrap(uint64_t x)
//@ requires true;
//@ ensures result == _wrap(x) &*& 0 <= result &*& result <= UINT_MAX;
{
  //@ div_rem(x, UINT_MAX);
  return x % UINT_MAX;
}



bool ip_addr_eq(void* k1, void* k2)
/*@ requires [?fr1]ether_addrp(k1, ?ea1) &*&
             [?fr2]ether_addrp(k2, ?ea2); @*/
/*@ ensures [fr1]ether_addrp(k1, ea1) &*&
            [fr2]ether_addrp(k2, ea2) &*&
            (result ? ea1 == ea2 : ea1 != ea2); @*/
{
  uint32_t* a = (uint32_t*) k1;
  uint32_t* b = (uint32_t*) k2;

  //@ open [fr1]ether_addrp(a, ea1);
  //@ open [fr2]ether_addrp(b, ea2);

  bool res = *a == *b;

  //@ close [fr1]ether_addrp(a, ea1);
  //@ close [fr2]ether_addrp(b, ea2);

  return res;
}

unsigned ip_addr_hash(void* k)
/*@ requires [?fr]ether_addrp(k, ?ea); @*/
/*@ ensures [fr]ether_addrp(k, ea) &*&
            result == eth_addr_hash(ea); @*/
{
  uint32_t* addr = (uint32_t*) k;

  //@ open [fr]ether_addrp(addr, ea);

  // Yes, this is necessary for VeriFast to understand that this cannot underflow...

  uint8_t a = *addr;
  //@ produce_limits(a);

  //@ close [fr]ether_addrp(addr, ea);

  uint64_t hash = 0;
  hash += a;

  hash = wrap(hash);
  return (uint32_t) hash;
}

void init_nothing_ea(void* entry)
/*@ requires chars(entry, sizeof(struct ether_addr), _); @*/
/*@ ensures ether_addrp(entry, _); @*/
{
  // Do nothing, just make VeriFast happy
  struct ether_addr* addr = (struct ether_addr*) entry;
  //@ close_struct(addr);
}

void init_nothing_dv(void* entry)
/*@ requires chars(entry, sizeof(struct DynamicValue), _); @*/
/*@ ensures dyn_valp(entry, _); @*/
{
  // Do nothing, just make VeriFast happy
  struct DynamicValue* dv = (struct DynamicValue*) entry;
  //@ close_struct(dv);
}

void init_nothing_st(void* entry)
/*@ requires chars(entry, sizeof(struct StaticKey), _); @*/
/*@ ensures static_keyp(entry, _); @*/
{
  // Do nothing, just make VeriFast happy
  struct StaticKey* key = (struct StaticKey*) entry;
  //@ close_struct(key);
}
