#include "bridge_data.h"

// Required to make VeriFast realize that if all items of a list are equal, the lists are equal
/*@ lemma void last_of_list_is_nil<t>(list<t> lst, int index)
    requires lst == cons(_, ?tail)
         &*& 0 <= index &*& index < length(lst);
    ensures (index == length(lst) - 1) == (tail == nil);
    {
      assume(false); // TODO
    }
@*/

// Required for VeriFast to not complain about underflows
static uint64_t wrap(uint64_t x)
//@ requires true;
//@ ensures result == _wrap(x) &*& 0 <= result &*& result <= UINT_MAX;
{
  //@ div_rem(x, UINT_MAX);
  return x % UINT_MAX;
}



bool ether_addr_eq(void* k1, void* k2)
/*@ requires [?fr1]ether_addrp(k1, ?ea1) &*&
             [?fr2]ether_addrp(k2, ?ea2); @*/
/*@ ensures [fr1]ether_addrp(k1, ea1) &*&
            [fr2]ether_addrp(k2, ea2) &*&
            (result ? ea1 == ea2 : ea1 != ea2); @*/
{
  struct ether_addr* a = (struct ether_addr*) k1;
  struct ether_addr* b = (struct ether_addr*) k2;

  //@ open [fr1]ether_addrp(a, eaddrc(?la));
  //@ open [fr2]ether_addrp(b, eaddrc(?lb));

  //@ last_of_list_is_nil(la, 5);
  //@ last_of_list_is_nil(lb, 5);

  bool res = a->addr_bytes[0] == b->addr_bytes[0]
          && a->addr_bytes[1] == b->addr_bytes[1]
          && a->addr_bytes[2] == b->addr_bytes[2]
          && a->addr_bytes[3] == b->addr_bytes[3]
          && a->addr_bytes[4] == b->addr_bytes[4]
          && a->addr_bytes[5] == b->addr_bytes[5];

  //@ close [fa]ether_addrp(a, _);
  //@ close [fb]ether_addrp(b, _);

  return res;
}

bool static_key_eq(void* k1, void* k2)
/*@ requires [?fr1]static_keyp(k1, ?sk1) &*&
             [?fr2]static_keyp(k2, ?sk2); @*/
/*@ ensures [fr1]static_keyp(k1, sk1) &*&
            [fr2]static_keyp(k2, sk2) &*&
            (result ? sk1 == sk2 : sk1 != sk2); @*/
{
  struct StaticKey* a = (struct StaticKey*) k1;
  struct StaticKey* b = (struct StaticKey*) k2;

  // Note that VeriFast refuses to have an && here, because ether_addr_eq is a call

  if (a->device != b->device) {
    return false;
  }

  return ether_addr_eq(&(a->addr), &(b->addr));
}

unsigned ether_addr_hash(void* k)
/*@ requires [?fr]ether_addrp(k, ?ea); @*/
/*@ ensures [fr]ether_addrp(k, ea) &*&
            result == eth_addr_hash(ea); @*/
{
  struct ether_addr* addr = (struct ether_addr*) k;

  //@ open [fr]ether_addrp(addr, _);

  // Yes, this is necessary for VeriFast to understand that this cannot underflow...

  uint8_t a = addr->addr_bytes[0];
  //@ produce_limits(a);
  uint8_t b = addr->addr_bytes[1];
  //@ produce_limits(b);
  uint8_t c = addr->addr_bytes[2];
  //@ produce_limits(c);
  uint8_t d = addr->addr_bytes[3];
  //@ produce_limits(d);
  uint8_t e = addr->addr_bytes[4];
  //@ produce_limits(e);
  uint8_t f = addr->addr_bytes[5];
  //@ produce_limits(f);

  //@ close [fr]ether_addrp(addr, _);

  uint64_t hash = 0;
  hash += a;
  hash *= 31;
  hash += b;
  hash *= 31;
  hash += c;
  hash *= 31;
  hash += d;
  hash *= 31;
  hash += e;
  hash *= 31;
  hash += f;

  hash = wrap(hash);
  return (uint32_t) hash;
}

unsigned static_key_hash(void* k)
/*@ requires [?fr]static_keyp(k, ?sk); @*/
/*@ ensures [fr]static_keyp(k, sk) &*&
            result == st_key_hash(sk); @*/
{
  struct StaticKey* key = (struct StaticKey*) k;

  // Once again, magic dance for VeriFast

  uint32_t ether_hash = ether_addr_hash(&(key->addr));
  //@ produce_limits(ether_hash);
  uint64_t device = (uint64_t) key->device;
  //@ produce_limits(device);

  uint64_t hash = 0;
  hash += ether_hash;
  hash *= 31;
  hash += device;

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
