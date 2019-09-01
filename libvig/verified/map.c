#include <stdlib.h>
#include <stddef.h>
#include "map.h"

#ifdef CAPACITY_POW2
#include "map-impl-pow2.h"
#else
#include "map-impl.h"
#endif

struct Map {
  int* busybits;
  void** keyps;
  unsigned* khs;
  int* chns;
  int* vals;
  unsigned capacity;
  unsigned size;
  map_keys_equality* keys_eq;
  map_key_hash* khash;
};

/*@
  predicate mapp<t>(struct Map* ptr,
                    predicate (void*;t) kp,
                    fixpoint (t,unsigned) hsh,
                    fixpoint (t,int,bool) recp,
                    mapi<t> map) =
    malloc_block_Map(ptr) &*&
    ptr->busybits |-> ?busybits &*&
    ptr->keyps |-> ?keyps &*&
    ptr->khs |-> ?khs &*&
    ptr->chns |-> ?chns &*&
    ptr->vals |-> ?vals &*&
    ptr->capacity |-> ?capacity &*&
    ptr->size |-> ?size &*&
    ptr->keys_eq |-> ?keys_eq &*&
    ptr->khash |-> ?khash &*&
    malloc_block_ints(busybits, capacity) &*&
    malloc_block_pointers(keyps, capacity) &*&
    malloc_block_uints(khs, capacity) &*&
    malloc_block_ints(chns, capacity) &*&
    malloc_block_ints(vals, capacity) &*&
    [_]is_map_keys_equality<t>(keys_eq, kp) &*&
    [_]is_map_key_hash<t>(khash, kp, hsh) &*&
    mapping(?m, ?addrs, kp, recp, hsh, capacity,
            busybits, keyps, khs, chns, vals) &*&
    size == length(m) &*&
    map == mapc(capacity, m, addrs)
#ifdef CAPACITY_POW2
    &*& is_pow2(capacity, N31) != none
#endif//CAPACITY_POW2
    ;
@*/

int map_allocate/*@ <t> @*/(map_keys_equality* keq, map_key_hash* khash,
                            unsigned capacity,
                            struct Map** map_out)
/*@ requires 0 < capacity &*& capacity < CAPACITY_UPPER_LIMIT &*&
             [_]is_map_keys_equality<t>(keq, ?kp) &*&
             [_]is_map_key_hash<t>(khash, kp, ?hsh) &*&
             *map_out |-> ?old_mo; @*/
/*@ ensures result == 0 ?
              *map_out |-> old_mo :
              (*map_out |-> ?new_mo &*&
               result == 1 &*&
               mapp<t>(new_mo, kp, hsh, nop_true,
                       mapc(capacity, nil, nil))); @*/
{

  #ifdef CAPACITY_POW2
  // Check that capacity is a power of 2
  if (capacity == 0 || (capacity & (capacity - 1)) != 0) {
      return 0;
  }
  //@ check_pow2_valid(capacity);
  #else
  #endif

  struct Map* old_map_val = *map_out;
  struct Map* map_alloc = (struct Map*) malloc(sizeof(struct Map));
  if (map_alloc == NULL) return 0;
  *map_out = (struct Map*) map_alloc;
  int* bbs_alloc = (int*) malloc(sizeof(int)*(int)capacity);
  if (bbs_alloc == NULL) {
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->busybits = bbs_alloc;
  void** keyps_alloc = (void**) malloc(sizeof(void*)*(int)capacity);
  if (keyps_alloc == NULL) {
    free(bbs_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->keyps = keyps_alloc;
  unsigned* khs_alloc = (unsigned*) malloc(sizeof(unsigned)*(int)capacity);
  if (khs_alloc == NULL) {
    free(keyps_alloc);
    free(bbs_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->khs = khs_alloc;
  int* chns_alloc = (int*) malloc(sizeof(int)*(int)capacity);
  if (chns_alloc == NULL) {
    free(khs_alloc);
    free(keyps_alloc);
    free(bbs_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->chns = chns_alloc;
  int* vals_alloc = (int*) malloc(sizeof(int)*(int)capacity);
  if (vals_alloc == NULL) {
    free(chns_alloc);
    free(khs_alloc);
    free(keyps_alloc);
    free(bbs_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->vals = vals_alloc;
  (*map_out)->capacity = capacity;
  (*map_out)->size = 0;
  (*map_out)->keys_eq = keq;
  (*map_out)->khash = khash;
  //@ close map_key_type<t>();
  //@ close map_key_hash<t>(hsh);
  //@ close map_record_property<t>(nop_true);
  map_impl_init((*map_out)->busybits,
                keq,
                (*map_out)->keyps,
                (*map_out)->khs,
                (*map_out)->chns,
                (*map_out)->vals,
                capacity);
  /*@
    close mapp<t>(*map_out, kp, hsh, nop_true, mapc(capacity, nil, nil));
    @*/
  return 1;
}

int map_get/*@ <t> @*/(struct Map* map, void* key, int* value_out)
/*@ requires mapp<t>(map, ?kp, ?hsh, ?recp,
                     mapc(?capacity, ?contents, ?addrs)) &*&
             kp(key, ?k) &*&
             *value_out |-> ?old_v; @*/
/*@ ensures mapp<t>(map, kp, hsh, recp,
                    mapc(capacity, contents, addrs)) &*&
            kp(key, k) &*&
            map_has_fp(contents, k) ?
              (result == 1 &*&
               *value_out |-> ?new_v &*&
               new_v == map_get_fp(contents, k)) :
              (result == 0 &*&
               *value_out |-> old_v); @*/
{
  //@ open mapp<t>(map, kp, hsh, recp, mapc(capacity, contents, addrs));
  map_key_hash* khash = map->khash;
  unsigned hash = khash(key);
  return map_impl_get(map->busybits,
                      map->keyps,
                      map->khs,
                      map->chns,
                      map->vals,
                      key,
                      map->keys_eq,
                      hash,
                      value_out,
                      map->capacity);
  //@ close mapp<t>(map, kp, hsh, recp, mapc(capacity, contents, addrs));
}

void map_put/*@ <t> @*/(struct Map* map, void* key, int value)
/*@ requires mapp<t>(map, ?kp, ?hsh, ?recp,
                     mapc(?capacity, ?contents, ?addrs)) &*&
             [0.25]kp(key, ?k) &*&
             true == recp(k, value) &*&
             length(contents) < capacity &*&
             false == map_has_fp(contents, k); @*/
/*@ ensures mapp<t>(map, kp, hsh, recp,
                    mapc(capacity, map_put_fp(contents, k, value),
                         map_put_fp(addrs, k, key))); @*/
{
  //@ open mapp<t>(map, kp, hsh, recp, mapc(capacity, contents, addrs));
  map_key_hash* khash = map->khash;
  unsigned hash = khash(key);
  map_impl_put(map->busybits,
               map->keyps,
               map->khs,
               map->chns,
               map->vals,
               key, hash, value,
               map->capacity);
  ++map->size;
  /*@ close mapp<t>(map, kp, hsh, recp, mapc(capacity,
                                             map_put_fp(contents, k, value),
                                             map_put_fp(addrs, k, key)));
  @*/
}

/*@
  lemma void map_erase_decrement_len<kt, vt>(list<pair<kt, vt> > m, kt k)
  requires true == map_has_fp(m, k);
  ensures length(m) == 1 + length(map_erase_fp(m, k));
  {
    switch(m) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key,val):
          if (key != k) map_erase_decrement_len(t, k);
        }
    }
  }
  @*/

/*@
  lemma void map_get_mem<kt,vt>(list<pair<kt,vt> > m, kt k)
  requires true == map_has_fp(m, k);
  ensures true == mem(pair(k, map_get_fp(m, k)), m);
  {
    switch(m) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key, val):
          if (key != k) map_get_mem(t, k);
        }
    }
  }
  @*/

void map_erase/*@ <t> @*/(struct Map* map, void* key, void** trash)
/*@ requires mapp<t>(map, ?kp, ?hsh, ?recp,
                     mapc(?capacity, ?contents, ?addrs)) &*&
             [?fk]kp(key, ?k) &*&
             *trash |-> _ &*&
             true == map_has_fp(contents, k); @*/
/*@ ensures mapp<t>(map, kp, hsh, recp,
                    mapc(capacity, map_erase_fp(contents, k),
                         map_erase_fp(addrs, k))) &*&
            [fk]kp(key, k) &*&
            *trash |-> ?k_out &*&
            k_out == map_get_fp(addrs, k) &*&
            false == map_has_fp(map_erase_fp(contents, k), k) &*&
            length(map_erase_fp(contents, k)) + 1 == length(contents) &*&
            [0.25]kp(k_out, k); @*/
{
  //@ open mapp<t>(map, kp, hsh, recp, mapc(capacity, contents, addrs));
  map_key_hash* khash = map->khash;
  unsigned hash = khash(key);
  map_impl_erase(map->busybits,
                 map->keyps,
                 map->khs,
                 map->chns,
                 key,
                 map->keys_eq,
                 hash,
                 map->capacity,
                 trash);
  //@ map_erase_decrement_len(contents, k);
  --map->size;
  /*@
    close mapp<t>(map, kp, hsh, recp, mapc(capacity,
                                           map_erase_fp(contents, k),
                                           map_erase_fp(addrs, k)));
    @*/
}

unsigned map_size/*@ <t> @*/(struct Map* map)
/*@ requires mapp<t>(map, ?kp, ?hsh, ?recp,
                     mapc(?capacity, ?contents, ?addrs)); @*/
/*@ ensures mapp<t>(map, kp, hsh, recp,
                    mapc(capacity, contents, addrs)) &*&
            result == length(contents); @*/
{
  //@ open mapp<t>(map, kp, hsh, recp, mapc(capacity, contents, addrs));
  return map->size;
  //@ close mapp<t>(map, kp, hsh, recp, mapc(capacity, contents, addrs));
}

/*@

  lemma void map_has_two_values_nondistinct<kt,vt>(list<pair<kt,vt> > m, kt k1, kt k2)
  requires true == map_has_fp(m, k1) &*&
          true == map_has_fp(m, k2) &*&
          map_get_fp(m, k1) == map_get_fp(m, k2) &*&
          k1 != k2;
  ensures false == distinct(map(snd, m));
  {
    switch(m) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key, value):
          if (key == k1) {
            map_get_mem(t, k2);
            mem_map(pair(k2, map_get_fp(m, k1)), t, snd);
          } else if (key == k2) {
            map_get_mem(t, k1);
            mem_map(pair(k1, map_get_fp(m, k2)), t, snd);
          } else {
            map_has_two_values_nondistinct(t, k1, k2);
          }
        }
    }
  }

@*/

/*@
  lemma void map_erase_keep_inv<kt,vt>(list<pair<kt, vt> > m,
                                       kt key,
                                       fixpoint (pair<kt, vt>, bool) inv)
  requires true == forall(m, inv);
  ensures true == forall(map_erase_fp(m, key), inv);
  {
    switch(m) {
      case nil:
      case cons(h,t):
        switch(h) {case pair(k, v): }
        map_erase_keep_inv(t, key, inv);
    }
  }

  lemma void map_erase_all_keep_inv<kt,vt>(list<pair<kt, vt> > m,
                                           list<kt> keys,
                                           fixpoint (pair<kt, vt>, bool) inv)
  requires true == forall(m, inv);
  ensures true == forall(map_erase_all_fp(m, keys), inv);
  {
    switch(keys) {
      case nil:
      case cons(h,t):
        map_erase_all_keep_inv(m, t, inv);
        map_erase_keep_inv(map_erase_all_fp(m, t), h, inv);
    }
  }
  @*/
