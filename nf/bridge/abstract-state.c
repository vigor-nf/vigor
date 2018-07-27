#include "lib/bridge-abstract-state.h"


/*@

lemma void bridge_expire_abstract(list<pair<ether_addri, uint32_t> > dyn_map,
                                  list<pair<uint16_t, bool> > vals,
                                  list<pair<ether_addri, bool> > keys,
                                  dchain indices,
                                  time_t time)
requires map_vec_chain_coherent(dyn_map, keys, indices);
ensures map_vec_chain_coherent(dyn_map, keys, indices) &*&
        set_eq(gen_dyn_entries(map_erase_all_fp
                                (dyn_map,
                                  vector_get_values_fp
                                    (keys, dchain_get_expired_indexes_fp
                                            (indices, time))),
                                vals,
                                dchain_expire_old_indexes_fp(indices, time)),
               expire_addresses(gen_dyn_entries(dyn_map, vals, indices),
                                time)) == true;
{
  assume(false);//TODO
}
@*/
/*@
                                          
lemma void alist_get_append_unrelevant(list<pair<int, time_t> > l,
                                       int i1, time_t time,
                                       int i2)
requires i1 != i2;
ensures alist_get_fp(append(l, cons(pair(i1, time), nil)), i2) == alist_get_fp(l, i2);
{
  switch(l) {
    case nil:
    case cons(h, t):
      switch(h) { case pair(idx,tm):
        if (idx != i2) alist_get_append_unrelevant(t, i1, time, i2);
      }
  }
}

lemma void dchaini_rejuv_alloc_other_keeps_time(list<pair<int, time_t> > alist,
                                                uint32_t index, time_t time,
                                                uint32_t cur_index)
requires index != cur_index;
ensures alist_get_fp(append(remove_by_index_fp(alist, index),
                            cons(pair(index, time), nil)), cur_index) ==
        alist_get_fp(alist, cur_index) &*&
        alist_get_fp(append(alist, cons(pair(index, time), nil)), cur_index) ==
        alist_get_fp(alist, cur_index);
{
  switch(alist) {
    case nil:
    case cons(h,t):
      switch(h) { case pair(idx,cur_time):
        if (idx != cur_index) {
          if (idx == index) {
            alist_get_append_unrelevant(t, index, time, cur_index);
            assert alist_get_fp(append(t, cons(pair(index, time), nil)), cur_index) ==
                   alist_get_fp(t, cur_index);
          } else {
            dchaini_rejuv_alloc_other_keeps_time(t, index, time, cur_index);
          }
        }
      }
  }
}

lemma void dchain_rejuv_alloc_other_keeps_time(dchain indices, uint32_t index,
                                               time_t time, uint32_t cur_index)
requires index != cur_index;
ensures dchain_get_time_fp(dchain_rejuvenate_fp(indices, index, time), cur_index) ==
        dchain_get_time_fp(indices, cur_index) &*&
        dchain_get_time_fp(dchain_allocate_fp(indices, index, time), cur_index) ==
        dchain_get_time_fp(indices, cur_index);
{
  switch(indices) {
    case dchain(alist, size, l, h):
      dchaini_rejuv_alloc_other_keeps_time(alist, index, time, cur_index);
  }
}

lemma void bridge_add_val_keep_dyn_entries(list<pair<ether_addri, uint32_t> > dyn_map,
                                           list<pair<uint16_t, bool> > vals,
                                           dchain indices,
                                           uint32_t index,
                                           uint16_t port,
                                           time_t time)
requires false == mem(index, map(snd, dyn_map));
ensures true == set_eq(gen_dyn_entries(dyn_map,
                                       update(index, pair(port, true), vals),
                                       dchain_allocate_fp(indices, index, time)),
                       gen_dyn_entries(dyn_map, vals, indices));
{
  switch(dyn_map) {
    case nil:
    case cons(h,t):
      switch(h) { case pair(cur_addr, cur_index):
        assert cur_index != index;
        bridge_add_val_keep_dyn_entries(t, vals, indices, index, port, time);
        nth_update_unrelevant(cur_index, index, pair(port, true), vals);
        dchain_rejuv_alloc_other_keeps_time(indices, index, time, cur_index);
        add_extra_preserves_subset
          (gen_dyn_entries(t,
                           update(index, pair(port, true), vals),
                           dchain_allocate_fp(indices, index, time)),
           gen_dyn_entries(t, vals, indices),
           dyn_entry(cur_addr,
                     fst(nth(cur_index, vals)),
                     dchain_get_time_fp(indices, cur_index)));
        add_extra_preserves_subset
          (gen_dyn_entries(t, vals, indices),
           gen_dyn_entries(t,
                           update(index, pair(port, true), vals),
                           dchain_allocate_fp(indices, index, time)),
           dyn_entry(cur_addr,
                     fst(nth(cur_index, vals)),
                     dchain_get_time_fp(indices, cur_index)));
      }
  }
}

lemma void dchaini_alloc_get_time_same(list<pair<int, time_t> > alist, int index, time_t time)
requires false == mem(index, map(fst, alist));
ensures alist_get_fp(append(alist, cons(pair(index, time), nil)), index) == time;
{
  switch(alist) {
    case nil:
    case cons(h,t): dchaini_alloc_get_time_same(t, index, time);
  }
}

lemma void dchain_alloc_get_time_same(dchain indices, int index, time_t time)
requires false == mem(index, dchain_indexes_fp(indices));
ensures dchain_get_time_fp(dchain_allocate_fp(indices, index, time), index) == time;
{
  switch(indices) { case dchain(alist, range, x1, x2):
    dchaini_alloc_get_time_same(alist, index, time);
  }
}

lemma void bridge_add_entry(list<pair<ether_addri, uint32_t> > dyn_map,
                            list<pair<uint16_t, bool> > vals,
                            dchain indices,
                            ether_addri addr,
                            uint32_t index,
                            uint16_t port,
                            time_t time)
requires false == mem(index, map(snd, dyn_map)) &*&
         false == mem(index, dchain_indexes_fp(indices)) &*&
         0 <= index &*& index < length(vals);
ensures set_eq(gen_dyn_entries(map_put_fp(dyn_map, addr, index),
                               update(index, pair(port, true), vals),
                               dchain_allocate_fp(indices, index, time)),
               add_dyn_entry(gen_dyn_entries(dyn_map, vals, indices),
                             addr, port, time)) == true;
{
  bridge_add_val_keep_dyn_entries(dyn_map, vals, indices, index, port, time);
  add_extra_preserves_subset(gen_dyn_entries(dyn_map,
                                        update(index, pair(port, true), vals),
                                        dchain_allocate_fp(indices, index, time)),
                             gen_dyn_entries(dyn_map, vals, indices),
                             dyn_entry(addr, port, time));
  nth_update(index, index, pair(port, true), vals);
  dchain_alloc_get_time_same(indices, index, time);
  add_extra_preserves_subset(gen_dyn_entries(dyn_map, vals, indices),
                             gen_dyn_entries(dyn_map,
                               update(index, pair(port, true), vals),
                               dchain_allocate_fp(indices, index, time)),
                             dyn_entry(addr, port, time));
}
@*/

/*@

lemma void alist_get_the_last_fp(list<pair<int, time_t> > alist, int index, time_t time)
requires false == mem(index, map(fst, alist));
ensures alist_get_fp(append(alist, cons(pair(index, time), nil)), index) == time;
{
  switch(alist) {
    case nil:
    case cons(h,t):
      alist_get_the_last_fp(t, index, time);
  }
}

lemma void dchaini_rejuv_time(list<pair<int, time_t> > alist, int index, time_t time)
requires true == distinct(map(fst, alist));
ensures alist_get_fp(append(remove_by_index_fp(alist, index),
                            cons(pair(index, time), nil)),
                     index) ==
        time;
{
  switch(alist) {
    case nil:
    case cons(h,t):
      if (fst(h) != index)
        dchaini_rejuv_time(t, index, time);
      else
        alist_get_the_last_fp(t, index, time);
  }
}

lemma void dchain_rejuv_time(dchain indices, int index, time_t time)
requires true == distinct(dchain_indexes_fp(indices));
ensures dchain_get_time_fp(dchain_rejuvenate_fp(indices, index, time), index) == time;
{
  switch(indices) {
    case dchain(alist, size, l, h):
      dchaini_rejuv_time(alist, index, time);
  }
}

lemma void bridge_dchain_rejuv_unrelevant_subset(list<pair<ether_addri, uint32_t> > dyn_map,
                                                 list<pair<uint16_t, bool> > vals,
                                                 dchain indices,
                                                 int index,
                                                 time_t time)
requires false == mem(index, map(snd, dyn_map));
ensures true == subset(gen_dyn_entries(dyn_map, vals,
                                       dchain_rejuvenate_fp(indices, index, time)),
                       gen_dyn_entries(dyn_map, vals, indices));
{
  switch(dyn_map) {
    case nil:
    case cons(h,t):
      switch(h) { case pair(cur_addr, cur_index):
        dchain_rejuv_alloc_other_keeps_time(indices, index, time, cur_index);
        bridge_dchain_rejuv_unrelevant_subset(t, vals, indices, index, time);
        add_extra_preserves_subset
          (gen_dyn_entries(t, vals, dchain_rejuvenate_fp(indices, index, time)),
           gen_dyn_entries(t, vals, indices),
           dyn_entry(cur_addr, fst(nth(cur_index, vals)),
                     dchain_get_time_fp(indices, cur_index)));

      }
  }
}

lemma void bridge_dchain_rejuv_unrelevant_superset(list<pair<ether_addri, uint32_t> > dyn_map,
                                                   list<pair<uint16_t, bool> > vals,
                                                   dchain indices,
                                                   int index,
                                                   time_t time)
requires false == mem(index, map(snd, dyn_map));
ensures true == subset(gen_dyn_entries(dyn_map, vals, indices),
                       gen_dyn_entries(dyn_map, vals,
                                       dchain_rejuvenate_fp(indices, index, time)));
{
  switch(dyn_map) {
    case nil:
    case cons(h,t):
      switch(h) { case pair(cur_addr, cur_index):
        dchain_rejuv_alloc_other_keeps_time(indices, index, time, cur_index);
        bridge_dchain_rejuv_unrelevant_superset(t, vals, indices, index, time);
        add_extra_preserves_subset
          (gen_dyn_entries(t, vals, indices),
           gen_dyn_entries(t, vals, dchain_rejuvenate_fp(indices, index, time)),
           dyn_entry(cur_addr, fst(nth(cur_index, vals)),
                     dchain_get_time_fp(dchain_rejuvenate_fp(indices,
                                                             index, time),
                                        cur_index)));

      }
  }
}
                     

lemma void map_get_contains_value<kt>(list<pair<kt, uint32_t> > m, kt k, uint32_t v)
requires map_get_fp(m, k) == v &*&
         true == mem(k, map(fst, m));
ensures true == mem(v, map(snd, m));
{
  switch(m) {
    case nil:
    case cons(h,t):
      switch(h) { case pair(key, value):
        if (key != k) map_get_contains_value(t, k, v);
      }
  }
}

lemma void bridge_dchain_rejuv_entry_subset
             (list<pair<ether_addri, uint32_t> > dyn_map,
              list<pair<uint16_t, bool> > vals,
              dchain indices,
              ether_addri addr,
              time_t time)
requires true == distinct(map(snd, dyn_map)) &*&
         true == distinct(dchain_indexes_fp(indices)) &*&
         true == mem(addr, map(fst, dyn_map));
ensures true == subset(gen_dyn_entries(dyn_map,
                                       vals,
                                       dchain_rejuvenate_fp(indices,
                                                            map_get_fp(dyn_map,
                                                                       addr),
                                                            time)),
                       rejuvenate_dyn_entry(gen_dyn_entries(dyn_map, vals,
                                                            indices),
                                            addr, time));
{
  switch(dyn_map) {
    case nil:
    case cons(h,t):
      switch(h) {
        case pair(cur_addr,cur_index):
          if (cur_addr == addr) {
            dchain_rejuv_time(indices, cur_index, time);
            bridge_dchain_rejuv_unrelevant_subset(t, vals, indices,
                                                  cur_index, time);
            add_extra_preserves_subset
              (gen_dyn_entries(t, vals, dchain_rejuvenate_fp(indices,
                                                             cur_index, time)),
               gen_dyn_entries(t, vals, indices),
               dyn_entry(cur_addr, fst(nth(cur_index, vals)), time));
          } else {
            bridge_dchain_rejuv_entry_subset(t, vals, indices, addr, time);
            add_extra_preserves_subset(gen_dyn_entries(t,
                                        vals,
                                        dchain_rejuvenate_fp
                                          (indices, map_get_fp(dyn_map, addr),
                                           time)),
                                       rejuvenate_dyn_entry
                                         (gen_dyn_entries(t, vals, indices),
                                          addr, time),
                                       dyn_entry(cur_addr,
                                                 fst(nth(cur_index, vals)),
                                                 dchain_get_time_fp(indices,
                                                                    cur_index)));
            if (map_get_fp(dyn_map, addr) != cur_index) {
              dchain_rejuv_alloc_other_keeps_time(indices, map_get_fp(dyn_map, addr),
                                                  time, cur_index);
            } else {
              map_get_contains_value(t, addr, cur_index);
            }
          }

      }
  }
}

lemma void bridge_dchain_rejuv_entry_superset
             (list<pair<ether_addri, uint32_t> > dyn_map,
              list<pair<uint16_t, bool> > vals,
              dchain indices,
              ether_addri addr,
              time_t time)
requires true == distinct(map(snd, dyn_map)) &*&
         true == distinct(dchain_indexes_fp(indices)) &*&
         true == mem(addr, map(fst, dyn_map));
ensures true == subset(rejuvenate_dyn_entry(gen_dyn_entries(dyn_map, vals,
                                                            indices),
                                            addr, time),
                       gen_dyn_entries(dyn_map,
                                       vals,
                                       dchain_rejuvenate_fp(indices,
                                                            map_get_fp(dyn_map,
                                                                       addr),
                                                            time)));
{
  switch(dyn_map) {
    case nil:
    case cons(h,t):
      switch(h) { case pair(cur_addr, cur_index):
        if (cur_addr == addr) {
          dchain_rejuv_time(indices, cur_index, time);
          bridge_dchain_rejuv_unrelevant_superset(t, vals, indices,
                                                  cur_index, time);
          add_extra_preserves_subset
            (gen_dyn_entries(t, vals, indices),
             gen_dyn_entries(t, vals, dchain_rejuvenate_fp
                                        (indices, map_get_fp(dyn_map, addr),
                                         time)),
             dyn_entry(cur_addr, fst(nth(cur_index, vals)), time));
        } else {
          if (cur_index == map_get_fp(dyn_map, addr)) {
            map_get_contains_value(t, addr, cur_index);
          }
          dchain_rejuv_alloc_other_keeps_time(indices, map_get_fp(dyn_map, addr),
                                              time, cur_index);
          bridge_dchain_rejuv_entry_superset(t, vals, indices, addr, time);
          add_extra_preserves_subset
            (rejuvenate_dyn_entry(gen_dyn_entries(t, vals, indices),
                                  addr, time),
             gen_dyn_entries(t, vals,
                             dchain_rejuvenate_fp(indices,
                                                  map_get_fp(dyn_map, addr),
                                                  time)),
             dyn_entry(cur_addr, fst(nth(cur_index, vals)),
                       dchain_get_time_fp
                         (dchain_rejuvenate_fp
                           (indices, map_get_fp(dyn_map, addr), time),
                          cur_index)));
        }
      }
  }
}

lemma void bridge_rejuv_entry(list<pair<ether_addri, uint32_t> > dyn_map,
                              list<pair<uint16_t, bool> > vals,
                              dchain indices,
                              ether_addri addr,
                              time_t time)
requires true == distinct(map(snd, dyn_map)) &*&
         true == distinct(dchain_indexes_fp(indices)) &*&
         true == mem(addr, map(fst, dyn_map));
ensures set_eq(gen_dyn_entries(dyn_map,
                               vals,
                               dchain_rejuvenate_fp(indices, map_get_fp(dyn_map, addr), time)),
               rejuvenate_dyn_entry(gen_dyn_entries(dyn_map, vals, indices),
                                    addr, time)) == true;
{
  bridge_dchain_rejuv_entry_subset(dyn_map, vals, indices, addr, time);
  bridge_dchain_rejuv_entry_superset(dyn_map, vals, indices, addr, time);
}

@*/

/*@
lemma void rejuv_unrelated_keep_mem(list<dyn_entry> dyn_table,
                                    ether_addri addr, time_t time,
                                    dyn_entry entry)
requires entry == dyn_entry(?e_addr, _, _) &*& addr != e_addr;
ensures mem(entry, dyn_table) == mem(entry, rejuvenate_dyn_entry(dyn_table, addr, time));
{
  switch(dyn_table) {
    case nil:
    case cons(h,t):
      switch(h) { case dyn_entry(cur_addr, cur_port, cur_time):
        if (cur_addr != addr)
          rejuv_unrelated_keep_mem(t, addr, time, entry);
      }
  }
                    
}

lemma void bridge_rejuv_entry_is_mem(list<dyn_entry> dyn_table, dyn_entry entry, time_t new_time)
requires true == mem(entry, dyn_table) &*& entry == dyn_entry(?cur_addr, ?cur_port, ?cur_time) &*&
         true == distinct(map(get_dyn_addr, dyn_table));
ensures true == mem(dyn_entry(cur_addr, cur_port, new_time),
                    rejuvenate_dyn_entry(dyn_table, cur_addr, new_time));
{
  switch(dyn_table) {
    case nil:
    case cons(h,t):
      switch(h) { case dyn_entry(h_addr, h_port, h_time):
        if (cur_addr != h_addr)
          bridge_rejuv_entry_is_mem(t, entry, new_time);
        else {
          if (h_port != cur_port) {
            mem_map(entry, t, get_dyn_addr);
          }
          assert h_port == cur_port;
          assert true == mem(dyn_entry(cur_addr, cur_port, new_time), rejuvenate_dyn_entry(dyn_table, cur_addr, new_time));
        }
      }
  }
}

lemma void bridge_rejuv_unrelated_keep_subset(list<dyn_entry> dyn_table1,
                                              list<dyn_entry> dyn_table2,
                                              ether_addri addr,
                                              time_t time)
requires false == mem(addr, map(get_dyn_addr, dyn_table1)) &*&
         true == subset(dyn_table1, dyn_table2);
ensures true == subset(dyn_table1, rejuvenate_dyn_entry(dyn_table2, addr, time));
{
  switch(dyn_table1) {
    case nil:
    case cons(h,t):
      switch(h) { case dyn_entry(h_addr, h_port, h_time):
        assert true == mem(h, dyn_table2);
        rejuv_unrelated_keep_mem(dyn_table2, addr, time, h); 
        bridge_rejuv_unrelated_keep_subset(t, dyn_table2, addr, time);
      }
  }
}

lemma void bridge_rejuv_entry_subset(list<dyn_entry> dyn_table1,
                                     list<dyn_entry> dyn_table2,
                                     ether_addri addr,
                                     time_t time)
requires true == subset(dyn_table1, dyn_table2) &*&
         true == distinct(map(get_dyn_addr, dyn_table1)) &*&
         true == distinct(map(get_dyn_addr, dyn_table2));
ensures true == subset(rejuvenate_dyn_entry(dyn_table1, addr, time),
                       rejuvenate_dyn_entry(dyn_table2, addr, time));
{
  switch(dyn_table1) {
    case nil:
    case cons(h,t):
      assert true == subset(t, dyn_table2);
      assert true == mem(h, dyn_table2);
      switch(h) { case dyn_entry(cur_addr, cur_port, cur_time):
        if (addr != cur_addr) {
          bridge_rejuv_entry_subset(t, dyn_table2, addr, time);
          assert true == subset(rejuvenate_dyn_entry(t, addr, time), rejuvenate_dyn_entry(dyn_table2, addr, time));
          rejuv_unrelated_keep_mem(dyn_table2, addr, time, h);
          assert true == mem(h, rejuvenate_dyn_entry(dyn_table2, addr, time));
        } else {
          bridge_rejuv_unrelated_keep_subset(t, dyn_table2, addr, time);
          assert true == subset(t, rejuvenate_dyn_entry(dyn_table2, addr, time));
          bridge_rejuv_entry_is_mem(dyn_table2, h, time);
          assert true == mem(dyn_entry(addr, cur_port, time), rejuvenate_dyn_entry(dyn_table2, addr, time));
        }
      }
  }
}

lemma void bridge_rejuv_entry_set_eq(list<dyn_entry> dyn_table1,
                                     list<dyn_entry> dyn_table2,
                                     ether_addri addr,
                                     time_t time)
requires true == set_eq(dyn_table1, dyn_table2) &*&
         true == distinct(map(get_dyn_addr, dyn_table1)) &*&
         true == distinct(map(get_dyn_addr, dyn_table2));
ensures true == set_eq(rejuvenate_dyn_entry(dyn_table1, addr, time),
                       rejuvenate_dyn_entry(dyn_table2, addr, time));
{
  bridge_rejuv_entry_subset(dyn_table1, dyn_table2, addr, time);
  bridge_rejuv_entry_subset(dyn_table2, dyn_table1, addr, time);
}
@*/
/*@
lemma void bridge_add_entry_set_eq(list<dyn_entry> dyn_table1,
                                    list<dyn_entry> dyn_table2,
                                    ether_addri addr,
                                    uint16_t port,
                                    time_t time)
requires true == set_eq(dyn_table1, dyn_table2);
ensures true == set_eq(add_dyn_entry(dyn_table1, addr, port, time),
                       add_dyn_entry(dyn_table2, addr, port, time));
{
  set_eq_cons(dyn_table1, dyn_table2, dyn_entry(addr, port, time));
}

@*/
/*@
lemma void stat_map_has(list<pair<stat_keyi, uint16_t> > map, stat_keyi key)
requires true;
ensures map_has_fp(map, key)== stat_table_has_key(gen_stat_entries(map), key);
{
  switch(map) {
    case nil:
    case cons(h,t):
      switch(h) {
        case pair(l,r):
          if (l != key) {
            stat_map_has(t, key);
          }
      }
  }
}
@*/
/*@
lemma void dyn_map_has(list<pair<ether_addri, int> > map,
                        list<pair<uint16_t, bool> > values,
                        dchain indices,
                        ether_addri key)
requires true;
ensures map_has_fp(map, key) == dyn_table_has_key(gen_dyn_entries(map, values, indices), key);
{
  switch(map) {
    case nil:
    case cons(h,t):
      switch(h) {
        case pair(l,r):
          if (l != key) {
            dyn_map_has(t, values, indices, key);
          }
      }
  }
}
@*/
/*@
lemma void stat_map_has_get(list<pair<stat_keyi, uint16_t> > map, stat_keyi key)
requires true == map_has_fp(map, key);
ensures true == stat_table_has_key(gen_stat_entries(map), key) &*&
        map_get_fp(map, key) == stat_table_get(gen_stat_entries(map), key);
{
  switch(map) {
    case nil:
    case cons(h,t):
      switch(h) {
        case pair(l,r):
          if (l != key) {
            stat_map_has_get(t, key);
          }
      }
  }
}

@*/
/*@
lemma void dyn_map_has_get(list<pair<ether_addri, int> > map,
                            list<pair<uint16_t, bool> > values,
                            dchain indices,
                            ether_addri key)
requires true == dyn_table_has_key(gen_dyn_entries(map, values, indices), key);
ensures true == map_has_fp(map, key) &*&
        fst(nth(map_get_fp(map, key), values)) == dyn_table_get(gen_dyn_entries(map, values, indices), key);
{
  switch(map) {
    case nil:
    case cons(h,t):
      switch(h) {
        case pair(l,r):
          if (l != key) {
            dyn_map_has_get(t, values, indices, key);
          }
      }
  }
}

@*/

/*@
  lemma void gen_dyn_entries_same_len(list<pair<ether_addri, int> > table,
                                      list<pair<uint16_t, bool> > values,
                                      dchain indices)
  requires true;
  ensures length(gen_dyn_entries(table, values, indices)) == length(table);
  {
    switch(table) {
      case nil: return;
      case cons(h, t):
        switch(h) { case pair(addr, index):
          gen_dyn_entries_same_len(t, values, indices);
        }
    }
  }
  @*/

/*@
lemma void chain_out_of_space_ml_out_of_space(mapi<ether_addri> dyn_map,
                                              list<pair<uint16_t, bool> > vals,
                                              dchain indices,
                                              mapi<stat_keyi> stat_map)
requires dyn_map == mapc(?dyn_capacity, ?dm, ?daddrs) &*&
         map_vec_chain_coherent(dm, ?heap, indices) &*&
         dyn_capacity == dchain_index_range_fp(indices);
ensures map_vec_chain_coherent(dm, heap, indices) &*&
        dchain_out_of_space_fp(indices) ==
        dyn_table_out_of_space(bridge_abstract_function(dyn_map, vals, indices, stat_map));
{
  switch(indices) {
    case dchain(alist, size, low, high):
      switch(dyn_map) { case mapc(dyn_capacity2, dm2, daddrs2):
        gen_dyn_entries_same_len(dm2, vals, indices);
        mvc_coherent_same_len(dm2, heap, indices);
        map_preserves_length(fst, alist);

        switch(stat_map) { case mapc(stat_capacity, sm, saddrs):}
      }
  }
}

@*/
