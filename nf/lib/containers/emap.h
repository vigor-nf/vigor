#ifndef _EMAP_H_INCLUDED_
#define _EMAP_H_INCLUDED_

#include "lib/nf_time.h"
#include "lib/containers/map.h"
#include "lib/containers/vector.h"
#include "lib/containers/double-chain.h"

/*@
  inductive emap<t> = emap(list<pair<t, int> > m, list<pair<t, real> > v, dchain ch);

  fixpoint emap<t> emap_expire_all<t>(emap<t> em, time_t t) {
    switch(em) { case emap(m, v, ch):
      return emap(map_erase_all_fp(m, vector_get_values_fp(v, dchain_get_expired_indexes_fp(ch, t))),
                  vector_erase_all_fp(v, dchain_get_expired_indexes_fp(ch, t)),
                  dchain_expire_old_indexes_fp(ch, t));
    }
  }

  fixpoint bool emap_has<t>(emap<t> em, t k) {
    switch(em) { case emap(m, v, ch):
      return map_has_fp(m, k);
    }
  }
  fixpoint int emap_get<t>(emap<t> em, t k) {
    switch(em) { case emap(m, v, ch):
      return map_get_fp(m, k);
    }
  }
  fixpoint emap<t> emap_rejuvenate_idx<t>(emap<t> em, int i, time_t t) {
    switch(em) { case emap(m, v, ch):
      return emap(m, v, dchain_rejuvenate_fp(ch, i, t));
    }
  }

  fixpoint emap<t> emap_erase<t>(emap<t> em, t k) {
    switch(em) { case emap(m, v, ch):
      return emap(map_erase_fp(m, k),
                  update(map_get_fp(m, k), pair(k, 1.0), v),
                  dchain_remove_index_fp(ch, map_get_fp(m, k)));
    }
  }

  fixpoint bool emap_has_index<t>(emap<t> em, int i) {
    switch(em) { case emap(m, v, ch):
      return dchain_allocated_fp(ch, i);
    }
  }

  fixpoint t emap_get_key<t>(emap<t> em, int i) {
    switch(em) { case emap(m, v, ch):
      return fst(nth(i, v));
    }
  }

  fixpoint emap<t> emap_allocate_int<t>(emap<t> em, time_t t, int i) {
    switch(em) { case emap(m, v, ch):
      return emap(m, v, dchain_allocate_fp(ch, i, t));
    }
  }

  fixpoint emap<t> emap_add_map<t>(emap<t> em, t k, int i) {
    switch(em) { case emap(m, v, ch):
      return emap(map_put_fp(m, k, i), update(i, pair(k, 0.75), v), ch);
    }
  }

  fixpoint bool emap_full<t>(emap<t> em) {
    switch(em) { case emap(m, v, ch):
      return dchain_out_of_space_fp(ch);
    }
  }
  @*/


#endif//_EMAP_H_INCLUDED_
