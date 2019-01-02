#ifndef _EMAP_H_INCLUDED_
#define _EMAP_H_INCLUDED_

#include "lib/nf_time.h"
#include "lib/containers/map.h"
#include "lib/containers/vector.h"
#include "lib/containers/double-chain.h"

/*@
  fixpoint list<pair<t, int> > emap_expire_all_map<t>(list<pair<t, int> > m, list<pair<t, real> > v, dchain ch, time_t t) {
    return map_erase_all_fp(m, vector_get_values_fp(v, dchain_get_expired_indexes_fp(ch, t)));
  }
  fixpoint list<pair<t, real> > emap_expire_all_vec<t>(list<pair<t, int> > m, list<pair<t, real> > v, dchain ch, time_t t) {
    return vector_erase_all_fp(v, dchain_get_expired_indexes_fp(ch, t));
  }
  fixpoint dchain emap_expire_all_chain<t>(list<pair<t, int> > m, list<pair<t, real> > v, dchain ch, time_t t) {
    return dchain_expire_old_indexes_fp(ch, t);
  }

  fixpoint bool emap_has<t>(list<pair<t, int> > m, list<pair<t, real> > v, dchain ch, t k) {
    return map_has_fp(m, k);
  }
  fixpoint int emap_get<t>(list<pair<t, int> > m, list<pair<t, real> > v, dchain ch, t k) {
    return map_get_fp(m, k);
  }
  fixpoint dchain emap_rejuvenate_chain<t>(list<pair<t, int> > m, list<pair<t, real> > v, dchain ch, t k, time_t t) {
    return dchain_rejuvenate_fp(ch, map_get_fp(m, k), t);
  }

  fixpoint list<pair<t, int> > emap_erase_map<t>(list<pair<t, int> > m, list<pair<t, real> > v, dchain ch, t k) {
    return map_erase_fp(m, k);
  }
  fixpoint list<pair<t, real> > emap_erase_vec<t>(list<pair<t, int> > m, list<pair<t, real> > v, dchain ch, t k) {
    return update(map_get_fp(m, k), pair(k, 1.0), v);
  }
  fixpoint dchain emap_erase_chain<t>(list<pair<t, int> > m, list<pair<t, real> > v, dchain ch, t k) {
    return dchain_remove_index_fp(ch, map_get_fp(m, k));
  }

  fixpoint bool emap_has_index<t>(list<pair<t, int> > m, list<pair<t, real> > v, dchain ch, int i) {
    return dchain_allocated_fp(ch, i);
  }

  fixpoint dchain emap_allocate_int<t>(list<pair<t, int> > m, list<pair<t, real> > v, dchain ch, time_t t, int i) {
    return dchain_allocate_fp(ch, i, t);
  }
  fixpoint list<pair<t, int> > emap_add_map<t>(list<pair<t, int> > m, list<pair<t, real> > v, dchain ch, t k, int i) {
    return map_put_fp(m, k, i);
  }
  fixpoint list<pair<t, real> > emap_add_vec<t>(list<pair<t, int> > m, list<pair<t, real> > v, dchain ch, t k, int i) {
    return update(i, pair(k, 0.75), v);
  }

  fixpoint bool emap_full<t>(list<pair<t, int> > m, list<pair<t, real> > v, dchain ch) {
    return dchain_out_of_space_fp(ch); //dchain_index_range_fp(ch) <= length(m);
  }
  @*/


#endif//_EMAP_H_INCLUDED_
