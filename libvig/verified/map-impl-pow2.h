#ifndef _MAP_IMPL_H_INCLUDED_
#define _MAP_IMPL_H_INCLUDED_

#include <stdbool.h>
#include "map-util.h"

//@ #include "../proof/map.gh"
//@ #include "../proof/stdex.gh"
//@ #include "../proof/mod-pow2.gh"

/*@ predicate pred_arg4<t1,t2,t3,t4>(predicate (t1,t2,t3,t4) p) = true;
    predicate pred_arg2<t1,t2>(predicate (t1,t2) p) = true;
  @*/

/*@
  // map<kt> = list<pair<kt,int> >;

  predicate mapping<kt>(list<pair<kt,int> > m,
                        list<pair<kt,void*> > addrs,
                        predicate (void*;kt) keyp,
                        fixpoint (kt,int,bool) recp,
                        fixpoint (kt,unsigned) hash,
                        unsigned capacity,
                        int* busybits,
                        void** keyps,
                        unsigned* k_hashes,
                        int* chns,
                        int* values);

@*/

/*@
  lemma void map_get_keeps_recp<kt>(list<pair<kt,int> > m, kt k);
  requires mapping(m, ?addrs, ?kp, ?rp, ?hsh,
                   ?cap, ?bbs, ?kps, ?khs, ?chns, ?vals) &*&
           true == map_has_fp(m, k);
  ensures true == rp(k, map_get_fp(m, k)) &*&
          mapping(m, addrs, kp, rp, hsh,
                  cap, bbs, kps, khs, chns, vals);
  @*/


/*@
  lemma void map_no_dup_keys<kt>(list<pair<kt, int> > m);
  requires mapping(m, ?addrs, ?kp, ?rp, ?hsh,
                   ?cap, ?bbs, ?kps, ?khs, ?chns, ?vals);
  ensures mapping(m, addrs, kp, rp, hsh,
                  cap, bbs, kps, khs, chns, vals) &*&
          true == no_dups(map(fst, m));
  @*/

/*@
  predicate map_key_type<kt>() = true;
  predicate map_key_hash<kt>(fixpoint (kt,unsigned) hsh) = true;
  predicate map_record_property<kt>(fixpoint(kt,int,bool) prop) = true;
  @*/


// Values and keys are void*, and the actual keys and values should be managed
// by the client application.
// I could not use integer keys, because need to operate with keys like
// int_key/ext_key that are much bigger than a 32bit integer.
void map_impl_init/*@ <kt> @*/ (int* busybits, map_keys_equality* cmp,
                                void** keyps, unsigned* khs, int* chns,
                                int* vals, unsigned capacity);
/*@ requires map_key_type<kt>() &*& map_key_hash<kt>(?hash) &*&
             [?fr]is_map_keys_equality<kt>(cmp, ?keyp) &*&
             map_record_property<kt>(?recp) &*&
             ints(busybits, capacity, ?bbs) &*&
             pointers(keyps, capacity, ?kplist) &*&
             ints(vals, capacity, ?vallist) &*&
             uints(khs, capacity, ?khlist) &*&
             ints(chns, capacity, ?chnlist) &*&
             0 < capacity &*& 2*capacity < INT_MAX; @*/
/*@ ensures mapping<kt>(empty_map_fp(), empty_map_fp(), keyp, recp, hash,
                        capacity, busybits, keyps,
                        khs, chns, vals) &*&
            [fr]is_map_keys_equality<kt>(cmp, keyp); @*/

int map_impl_get/*@ <kt> @*/(int* busybits, void** keyps,
                             unsigned* k_hashes, int* chns,
                             int* values,
                             void* keyp, map_keys_equality* eq,
                             unsigned hash, int* value,
                             unsigned capacity);
/*@ requires mapping<kt>(?m, ?addrs, ?kp, ?recp, ?hsh, capacity, busybits,
                         keyps, k_hashes, chns, values) &*&
             [?fk]kp(keyp, ?k) &*&
             [?fr]is_map_keys_equality(eq, kp) &*&
             hsh(k) == hash &*&
             *value |-> ?v &*&
             is_pow2(capacity, N31) != none; @*/
/*@ ensures mapping<kt>(m, addrs, kp, recp, hsh, capacity, busybits,
                        keyps, k_hashes, chns, values) &*&
            [fk]kp(keyp, k) &*&
            [fr]is_map_keys_equality(eq, kp) &*&
            (map_has_fp(m, k) ?
             (result == 1 &*&
              *value |-> ?nv &*&
              nv == map_get_fp(m, k) &*&
              true == recp(k, nv)):
             (result == 0 &*&
              *value |-> v)); @*/

void map_impl_put/*@ <kt> @*/(int* busybits, void** keyps,
                              unsigned* k_hashes, int* chns,
                              int* values,
                              void* keyp, unsigned hash, int value,
                              unsigned capacity);
/*@ requires mapping<kt>(?m, ?addrs, ?kp, ?recp, ?hsh, capacity, busybits,
                         keyps, k_hashes, chns, values) &*&
             [0.25]kp(keyp, ?k) &*& true == recp(k, value) &*&
             hsh(k) == hash &*&
             false == map_has_fp(m, k) &*&
             map_size_fp(m) < capacity &*&
             is_pow2(capacity, N31) != none; @*/
/*@ ensures true == recp(k, value) &*&
            mapping<kt>(map_put_fp(m, k, value),
                        map_put_fp(addrs, k, keyp),
                        kp, recp,
                        hsh,
                        capacity, busybits,
                        keyps, k_hashes, chns, values); @*/

//TODO: Keep track of the key pointers, in order to preserve the pointer value
// when releasing it with map_impl_erase.
void map_impl_erase/*@ <kt> @*/(int* busybits, void** keyps, unsigned* key_hashes,
                                int* chns,
                                void* keyp, map_keys_equality* eq, unsigned hash,
                                unsigned capacity,
                                void** keyp_out);
/*@ requires mapping<kt>(?m, ?addrs, ?kp, ?recp, ?hsh, capacity, busybits,
                         keyps, key_hashes, chns, ?values) &*&
             [?fk]kp(keyp, ?k) &*&
             [?fr]is_map_keys_equality<kt>(eq, kp) &*&
             hsh(k) == hash &*&
             *keyp_out |-> ?ko &*&
             true == map_has_fp(m, k) &*&
             is_pow2(capacity, N31) != none; @*/
/*@ ensures [fk]kp(keyp, k) &*&
            [fr]is_map_keys_equality<kt>(eq, kp) &*&
            *keyp_out |-> ?nko &*&
            nko == map_get_fp(addrs, k) &*&
            [0.25]kp(nko, k) &*&
            false == map_has_fp(map_erase_fp(m, k), k) &*&
            mapping<kt>(map_erase_fp(m, k),
                        map_erase_fp(addrs, k),
                        kp, recp, hsh,
                        capacity, busybits, keyps, key_hashes, chns, values); @*/

unsigned map_impl_size/*@ <kt> @*/(int* busybits, unsigned capacity);
/*@ requires mapping<kt>(?m, ?addrs, ?kp, ?recp, ?hsh, capacity, busybits,
                         ?keyps, ?k_hashes, ?chns, ?values); @*/
/*@ ensures mapping<kt>(m, addrs, kp, recp, hsh, capacity, busybits,
                        keyps, k_hashes, chns, values) &*&
            result == map_size_fp(m);@*/

#endif //_MAP_IMPL_H_INCLUDED_
