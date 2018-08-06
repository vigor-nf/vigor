#include "lib/containers/double-chain.h"
#include "lib/coherence.h"
#include "lib/nf_time.h"
#include "lb_balancer.h"

/*@
  inductive lb_entry = lb_entry(lb_flowi, lb_backendi, time_t);

  inductive lb_table = lb_table(list<lb_entry>, int);

  fixpoint list<lb_entry> get_lb_table(lb_table table) {
    switch(table) {
      case lb_table(lb_entries, capacity):
        return lb_entries;
    }
  }

  fixpoint bool lb_table_has_key(list<lb_entry> entries, lb_flowi key) {
    switch(entries) {
      case nil: return false;
      case cons(h,t):
        return switch(h) { case lb_entry(k,v,timestamp):
           return (k == key) ? true : lb_table_has_key(t, key);
        };
    }
  }

  fixpoint bool lb_table_out_of_space(lb_table t) {
    switch(t) { case lb_table(lb_entries, capacity):
      return capacity <= length(lb_entries);
    }
  }

  fixpoint lb_backendi lb_table_get(list<lb_entry> entries, lb_flowi key) {
    switch(entries) {
      case nil: return lb_backendc(0);
      case cons(h,t):
        return switch(h) { case lb_entry(k,v,timestamp):
           return (k == key) ? v : lb_table_get(t, key);
        };
    }
  }

  fixpoint list<lb_entry> gen_lb_entries(list<pair<lb_flowi, int> > table,
                                         list<pair<lb_backendi, bool> > values,
                                         dchain indices) {
    switch(table) {
      case nil: return nil;
      case cons(h, t): return switch(h) { case pair(flow, index):
        return cons(lb_entry(flow,
                             fst(nth(index, values)),
                             dchain_get_time_fp(indices, index)),
                    gen_lb_entries(t, values, indices));
      };
    }
  }


  fixpoint lb_table lb_abstract_function(mapi<lb_flowi> lb_map,
                                         list<pair<lb_backendi, bool> > vals,
                                         dchain indices) {
    switch(lb_map) { case mapc(capacity, dm, dflows):
        return lb_table(gen_lb_entries(dm, vals, indices), capacity);
    }
  }


  fixpoint list<lb_entry> add_lb_entry(list<lb_entry> table,
                                       lb_flowi flow,
                                       lb_backendi backend,
                                       time_t time) {

    return cons(lb_entry(flow, backend, time), table);
  }

  fixpoint list<lb_entry> rejuvenate_lb_entry(list<lb_entry> table,
                                              lb_flowi flow_to_rej,
                                              time_t new_time) {
    switch(table) {
      case nil: return nil;
      case cons(h,t):
        return switch(h) { case lb_entry(flow, backend, time):
          return (flow == flow_to_rej) ?
                   cons(lb_entry(flow, backend, new_time), t) :
                   cons(h, rejuvenate_lb_entry(t, flow_to_rej, new_time));
        };
    }
  }

  fixpoint list<lb_entry> expire_lb_entries(list<lb_entry> table, time_t now) {
    switch(table) {
      case nil: return nil;
      case cons(h,t):
        return switch(h) { case lb_entry(flow, backend, time):
          return (time < now) ? expire_lb_entries(t, now) : cons(h, expire_lb_entries(t, now));
        };
    }
  }

  lemma void lb_expire_abstract(list<pair<lb_flowi, uint32_t> > lb_map,
                                list<pair<lb_backendi, bool> > vals,
                                list<pair<lb_flowi, bool> > keys,
                                dchain indices,
                                time_t time);
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

  lemma void lb_add_entry(list<pair<lb_flowi, uint32_t> > lb_map,
                          list<pair<lb_backendi, bool> > vals,
                          dchain indices,
                          lb_flowi flow,
                          uint32_t index,
                          lb_backendi backend,
                          time_t time);
  requires true;
  ensures set_eq(gen_lb_entries(map_put_fp(lb_map, flow, index),
                                update(index, pair(backend, true), vals),
                                dchain_allocate_fp(indices, index, time)),
                 add_lb_entry(gen_lb_entries(lb_map, vals, indices),
                              flow, backend, time)) == true;

  lemma void lb_rejuv_entry(list<pair<lb_flowi, uint32_t> > lb_map,
                            list<pair<lb_backendi, bool> > vals,
                            dchain indices,
                            lb_flowi flow,
                            time_t time);
  requires true;
  ensures set_eq(gen_lb_entries(lb_map,
                                vals,
                                dchain_rejuvenate_fp(indices, map_get_fp(lb_map, flow), time)),
                 rejuvenate_lb_entry(gen_lb_entries(lb_map, vals, indices),
                                     flow, time)) == true;

  lemma void lb_rejuv_entry_set_eq(list<lb_entry> lb_table1,
                                   list<lb_entry> lb_table2,
                                   lb_flowi flow,
                                   time_t time);
  requires true == set_eq(lb_table1, lb_table2);
  ensures true == set_eq(rejuvenate_lb_entry(lb_table1, flow, time),
                         rejuvenate_lb_entry(lb_table2, flow, time));

  lemma void lb_add_entry_set_eq(list<lb_entry> lb_table1,
                                 list<lb_entry> lb_table2,
                                 lb_flowi flow,
                                 lb_backendi backend,
                                 time_t time);
  requires true == set_eq(lb_table1, lb_table2);
  ensures true == set_eq(add_lb_entry(lb_table1, flow, backend, time),
                         add_lb_entry(lb_table2, flow, backend, time));

  lemma void lb_map_has(list<pair<lb_flowi, uint32_t> > map,
                        list<pair<lb_backendi, bool> > values,
                        dchain indices,
                        lb_flowi key);
  requires true;
  ensures map_has_fp(map, key) == lb_table_has_key(gen_lb_entries(map, values, indices), key);

  lemma void lb_map_has_get(list<pair<lb_flowi, uint32_t> > map,
                            list<pair<lb_backendi, bool> > values,
                            dchain indices,
                            lb_flowi key);
  requires true == lb_table_has_key(gen_lb_entries(map, values, indices), key);
  ensures true == map_has_fp(map, key) &*&
          fst(nth(map_get_fp(map, key), values)) == lb_table_get(gen_lb_entries(map, values, indices), key);

  lemma void chain_out_of_space_lb_out_of_space(mapi<lb_flowi> lb_map,
                                                list<pair<lb_backendi, bool> > vals,
                                                dchain indices);
  requires true;
  ensures dchain_out_of_space_fp(indices) ==
          lb_table_out_of_space(lb_abstract_function(lb_map, vals, indices));
@*/
