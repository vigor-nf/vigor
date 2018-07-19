#ifndef _MAP_UTIL_H_INCLUDED_
#define _MAP_UTIL_H_INCLUDED_

#define CAPACITY_UPPER_LIMIT 140000

// Here the return type of a hash function is assumed to be unsigned = uint32_t
// If you want to change it, you can run find&replace for unsigned in map
// related files, just be careful not to mix the type of the map capacity and
// a couple of other unsigned unrelated values.

typedef unsigned map_key_hash/*@ <K>(predicate (void*; K) keyp,
                                     fixpoint (K, unsigned) hash) @*/(void* k1);
//@ requires [?fr]keyp(k1, ?kk1);
//@ ensures [fr]keyp(k1, kk1) &*& result == hash(kk1);

#endif//_MAP_UTIL_H_INCLUDED_
