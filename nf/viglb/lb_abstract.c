#include "lb_abstract.h"

/*@
  lemma void lb_expire_abstract(list<pair<lb_flowi, uint32_t> > lb_map,
                                list<pair<lb_backendi, bool> > vals,
                                list<pair<lb_flowi, bool> > keys,
                                dchain indices,
                                time_t time)
  requires true;
  ensures set_eq(gen_lb_entries(map_erase_all_fp
                                  (lb_map,
                                   vector_get_values_fp
                                     (keys, dchain_get_expired_indexes_fp
                                              (indices, time))),
                                 vals,
                                 dchain_expire_old_indexes_fp(indices, time)),
                 expire_lb_entries(gen_lb_entries(lb_map, vals, indices),
                                  time)) == true;
  {
    assume(false);
  }

  lemma void lb_add_entry(list<pair<lb_flowi, uint32_t> > lb_map,
                          list<pair<lb_backendi, bool> > vals,
                          dchain indices,
                          lb_flowi flow,
                          uint32_t index,
                          lb_backendi backend,
                          time_t time)
  requires true;
  ensures set_eq(gen_lb_entries(map_put_fp(lb_map, flow, index),
                                update(index, pair(backend, true), vals),
                                dchain_allocate_fp(indices, index, time)),
                 add_lb_entry(gen_lb_entries(lb_map, vals, indices),
                              flow, backend, time)) == true;
  {
    assume(false);
  }

  lemma void lb_rejuv_entry(list<pair<lb_flowi, uint32_t> > lb_map,
                            list<pair<lb_backendi, bool> > vals,
                            dchain indices,
                            lb_flowi flow,
                            time_t time)
  requires true;
  ensures set_eq(gen_lb_entries(lb_map,
                                vals,
                                dchain_rejuvenate_fp(indices, map_get_fp(lb_map, flow), time)),
                 rejuvenate_lb_entry(gen_lb_entries(lb_map, vals, indices),
                                     flow, time)) == true;
  {
    assume(false);
  }

  lemma void lb_rejuv_entry_set_eq(list<lb_entry> lb_table1,
                                   list<lb_entry> lb_table2,
                                   lb_flowi flow,
                                   time_t time)
  requires true == set_eq(lb_table1, lb_table2);
  ensures true == set_eq(rejuvenate_lb_entry(lb_table1, flow, time),
                         rejuvenate_lb_entry(lb_table2, flow, time));
  {
    assume(false);
  }

  lemma void lb_add_entry_set_eq(list<lb_entry> lb_table1,
                                 list<lb_entry> lb_table2,
                                 lb_flowi flow,
                                 lb_backendi backend,
                                 time_t time)
  requires true == set_eq(lb_table1, lb_table2);
  ensures true == set_eq(add_lb_entry(lb_table1, flow, backend, time),
                         add_lb_entry(lb_table2, flow, backend, time));
  {
    assume(false);
  }

  lemma void lb_map_has(list<pair<lb_flowi, uint32_t> > map,
                        list<pair<lb_backendi, bool> > values,
                        dchain indices,
                        lb_flowi key)
  requires true;
  ensures map_has_fp(map, key) == lb_table_has_key(gen_lb_entries(map, values, indices), key);
  {
    assume(false);
  }

  lemma void lb_map_has_get(list<pair<lb_flowi, uint32_t> > map,
                            list<pair<lb_backendi, bool> > values,
                            dchain indices,
                            lb_flowi key)
  requires true == lb_table_has_key(gen_lb_entries(map, values, indices), key);
  ensures true == map_has_fp(map, key) &*&
          fst(nth(map_get_fp(map, key), values)) == lb_table_get(gen_lb_entries(map, values, indices), key);
  {
    assume(false);
  }

  lemma void chain_out_of_space_lb_out_of_space(mapi<lb_flowi> lb_map,
                                                list<pair<lb_backendi, bool> > vals,
                                                dchain indices)
  requires true;
  ensures dchain_out_of_space_fp(indices) ==
          lb_table_out_of_space(lb_abstract_function(lb_map, vals, indices));
  {
    assume(false);
  }

@*/
