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

  fixpoint list<pair<t, int> > emap_erase_map<t>(list<pair<t, int> > m, list<pair<t, real> > v, dchain ch, t k);
  fixpoint list<pair<t, real> > emap_erase_vec<t>(list<pair<t, int> > m, list<pair<t, real> > v, dchain ch, t k);
  fixpoint dchain emap_erase_chain<t>(list<pair<t, int> > m, list<pair<t, real> > v, dchain ch, t k);

  fixpoint bool emap_has_index<t>(list<pair<t, int> > m, list<pair<t, real> > v, dchain ch, int i) {
    return dchain_allocated_fp(ch, i);
  }

  fixpoint int emap_get_next_int<t>(list<pair<t, int> > m, list<pair<t, real> > v, dchain ch);
  fixpoint dchain emap_allocate_int<t>(list<pair<t, int> > m, list<pair<t, real> > v, dchain ch, time_t t);
  fixpoint list<pair<t, int> > emap_add_map<t>(list<pair<t, int> > m, list<pair<t, real> > v, dchain ch, int i, t k);
  fixpoint list<pair<t, real> > emap_add_vec<t>(list<pair<t, int> > m, list<pair<t, real> > v, dchain ch, int i, t k);

  fixpoint bool emap_full<t>(list<pair<t, int> > m, list<pair<t, real> > v, dchain ch) {
    return dchain_index_range_fp(ch) <= length(m);
  }
  @*/


#endif//_EMAP_H_INCLUDED_
