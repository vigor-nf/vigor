#ifndef _EMAP_H_INCLUDED_
#define _EMAP_H_INCLUDED_

#include "vigor-time.h"
#include "map.h"
#include "vector.h"
#include "double-chain.h"
#include "cht.h"

/*@
  inductive emap<T> = emap(list<pair<T, int> > m, list<pair<T, real> > v, dchain ch);

  fixpoint emap<T> emap_expire_all<T>(emap<T> em, vigor_time_t t) {
    switch(em) { case emap(m, v, ch):
      return emap(map_erase_all_fp(m, vector_get_values_fp(v, dchain_get_expired_indexes_fp(ch, t))),
                  vector_erase_all_fp(v, dchain_get_expired_indexes_fp(ch, t)),
                  dchain_expire_old_indexes_fp(ch, t));
    }
  }

  fixpoint bool emap_has<T>(emap<T> em, T k) {
    switch(em) { case emap(m, v, ch):
      return map_has_fp(m, k);
    }
  }

  fixpoint int emap_get<T>(emap<T> em, T k) {
    switch(em) { case emap(m, v, ch):
      return map_get_fp(m, k);
    }
  }

  fixpoint emap<T> emap_refresh_idx<T>(emap<T> em, int i, vigor_time_t t) {
    switch(em) { case emap(m, v, ch):
      return emap(m, v, dchain_rejuvenate_fp(ch, i, t));
    }
  }

  fixpoint emap<T> emap_erase<T>(emap<T> em, T k) {
    switch(em) { case emap(m, v, ch):
      return emap(map_erase_fp(m, k),
                  update(map_get_fp(m, k), pair(k, 1.0), v),
                  dchain_remove_index_fp(ch, map_get_fp(m, k)));
    }
  }

  fixpoint bool emap_has_idx<T>(emap<T> em, int i) {
    switch(em) { case emap(m, v, ch):
      return dchain_allocated_fp(ch, i);
    }
  }

  fixpoint T emap_get_key<T>(emap<T> em, int i) {
    switch(em) { case emap(m, v, ch):
      return fst(nth(i, v));
    }
  }

  fixpoint emap<T> emap_add<T>(emap<T> em, T k, int i, vigor_time_t t) {
    switch(em) { case emap(m, v, ch):
      return emap(map_put_fp(m, k, i), update(i, pair(k, 0.75), v), dchain_allocate_fp(ch, i, t));
    }
  }

  fixpoint bool emap_full<T>(emap<T> em) {
    switch(em) { case emap(m, v, ch):
      return dchain_out_of_space_fp(ch);
    }
  }

  // Consistent hashing table-related

  fixpoint bool emap_exists_with_cht<T>(emap<T> em, list<pair<uint32_t, real> > cht, int hash) {
    switch(em) { case emap(m, v, ch):
      return cht_exists(hash, cht, ch);
    }
  }

  fixpoint int emap_choose_with_cht<T>(emap<T> em, list<pair<uint32_t, real> > cht, int hash) {
    switch(em) { case emap(m, v, ch):
      return cht_choose(hash, cht, ch);
    }
  }

  // Vector
  inductive vector<T> = vector(list<pair<T, real> >);

  fixpoint T vector_get<T>(vector<T> v, int i) {
    switch(v) { case vector(l):
      return fst(nth(i, l));
    }
  }

  fixpoint vector<T> vector_set<T>(vector<T> vec, int i, T val) {
    switch(vec) { case vector(l):
      return vector(update(i, pair(val, 1.0), l));
    }
  }
  @*/


#endif//_EMAP_H_INCLUDED_
