#include "lib/bridge-abstract-state.h"
//@ #include "lib/containers/multiset.gh"


/*@
fixpoint list<dyn_entry> erase_address(list<dyn_entry> entries, ether_addri address) {
  switch(entries) {
    case nil: return entries;
    case cons(h,t): return switch(h) { case dyn_entry(cur_addr, port, time):
      return cur_addr == address  ?
        erase_address(t, address) :
        cons(h, erase_address(t, address));
    };
  }
}

fixpoint list<dyn_entry> erase_addresses(list<dyn_entry> entries, list<ether_addri> addresses) {
  switch(addresses) {
    case nil: return entries;
    case cons(h,t): return erase_address(erase_addresses(entries, t), h);
  }
}

@*/

/*@
lemma void erase_addresses_nil(list<ether_addri> addrs)
requires true;
ensures erase_addresses(nil, addrs) == nil;
{
  switch(addrs) {
    case nil:
    case cons(h,t):
      erase_addresses_nil(t);
  }
}
@*/

/*@
lemma void dchaini_expired_in_expired(list<pair<int, time_t> > alist, int index, time_t time)
requires true == distinct(map(fst, alist)) &*&
         true == exists(alist, (same_index)(index));
ensures (alist_get_fp(alist, index) < time) ==
        mem(index, map(fst, filter((is_cell_expired)(time), alist)));
{
  switch(alist) {
    case nil:
    case cons(h,t): switch(h) { case pair(cur_index, cur_time):
      if (cur_index == index) {
        if (time <= cur_time) {
          filter_subset((is_cell_expired)(time), t);
          subset_map(filter((is_cell_expired)(time), t), t, fst);
          if (mem(index, map(fst, filter((is_cell_expired)(time), t)))) {
            subset_mem_trans(map(fst, filter((is_cell_expired)(time), t)), map(fst, t), index);
          }
          assert false == mem(index, map(fst, filter((is_cell_expired)(time), t)));
        }
      } else {
        dchaini_expired_in_expired(t, index, time);
      }
    }
  }
}

lemma void dchain_expired_in_expired(dchain ch, int index, time_t t)
requires true == distinct(dchain_indexes_fp(ch)) &*&
         true == dchain_allocated_fp(ch, index);
ensures (dchain_get_time_fp(ch, index) < t) == (mem(index, dchain_get_expired_indexes_fp(ch, t)));
{
  switch(ch) { case dchain(alist, x1, x2, x3):
    dchaini_expired_in_expired(alist, index, t);
  }
}
@*/

/*@
lemma void vector_get_values_index_of<t>(list<pair<t, bool> > v, list<int> indices, t entry)
requires true == mem(entry, vector_get_values_fp(v, indices));
ensures fst(nth(nth(index_of(entry, vector_get_values_fp(v, indices)), indices), v)) == entry;
{
  switch(indices) {
    case nil:
    case cons(h,t):
      if (fst(nth(h, v)) != entry) {
        vector_get_values_index_of(v, t, entry);
      }
  }
}
@*/

/*@
lemma void vector_get_values_known<t>(list<pair<t, bool> > v, list<int> indices, int idx)
requires true == mem(idx, indices);
ensures true == mem(fst(nth(idx, v)), vector_get_values_fp(v, indices));
{
  switch(indices) {
    case nil:
    case cons(h,t):
      if (h != idx) {
        vector_get_values_known(v, t, idx);
      }
  }
}
@*/

/*@
lemma void erase_addresses_cons(dyn_entry e, list<dyn_entry> entries, list<ether_addri> addrs)
requires true;
ensures (mem(get_dyn_addr(e), addrs)) ?
        erase_addresses(cons(e, entries), addrs) == erase_addresses(entries, addrs) :
        erase_addresses(cons(e, entries), addrs) == cons(e, erase_addresses(entries, addrs));
{
  switch(addrs) {
    case nil:
    case cons(h,t):
      switch(e) { case dyn_entry(e_addr, e_port, e_time):
        erase_addresses_cons(e, entries, t);
      }
  }
}

lemma void erase_addresses_known(dyn_entry e, list<dyn_entry> entries, list<ether_addri> addrs)
requires true == mem(get_dyn_addr(e), addrs);
ensures erase_addresses(cons(e, entries), addrs) == erase_addresses(entries, addrs);
{
  switch(addrs) {
    case nil:
    case cons(h,t):
      switch(e) { case dyn_entry(e_addr, e_port, e_time):
        if (e_addr == h) {
          erase_addresses_cons(e, entries, t);
        } else {
          erase_addresses_known(e, entries, t);
        }
      }
  }
}
@*/

/*@
lemma void erase_non_existent_address(list<dyn_entry> entries, ether_addri addr)
requires false == mem(addr, map(get_dyn_addr, entries));
ensures erase_address(entries, addr) == entries;
{
  switch(entries) {
    case nil:
    case cons(h,t):
      switch(h) { case dyn_entry(e_addr, e_port, e_time):
        erase_non_existent_address(t, addr);
      }
  }
}
@*/

/*@
lemma void map_no_addr_gen_dyn_entries_no_addr(list<pair<ether_addri, uint32_t> > m,
                                               list<pair<uint16_t, bool> > v,
                                               dchain ch,
                                               ether_addri addr)
requires false == mem(addr, map(fst, m));
ensures false == mem(addr, map(get_dyn_addr, gen_dyn_entries(m, v, ch)));
{
  switch(m) {
    case nil:
    case cons(h,t):
      switch(h) { case pair(key, value):
        map_no_addr_gen_dyn_entries_no_addr(t, v, ch, addr);
      }
  }
}
@*/

/*@
lemma void two_indexes_into_engaged_nondistinct(list<pair<ether_addri, bool> > keys, int i1, int i2)
requires i1 != i2 &*&
         0 <= i1 &*& i1 < length(keys) &*&
         0 <= i2 &*& i2 < length(keys) &*&
         true == engaged_cell(nth(i1, keys)) &*&
         true == engaged_cell(nth(i2, keys)) &*&
         fst(nth(i1, keys)) == fst(nth(i2, keys));
ensures false == distinct(map(fst, filter(engaged_cell, keys)));
{
  switch(keys) {
    case nil:
    case cons(h,t):
      switch(h) { case pair(val, owned):
        if (i1 == 0) {
          switch(nth(i2 - 1, t)) { case pair(aaa,bbb): }
          filter_mem(pair(val, false), t, engaged_cell);
          mem_map(pair(val, false), filter(engaged_cell, t), fst);
        } else if (i2 == 0) {
          switch(nth(i1 - 1, t)) { case pair(aaa,bbb): }
          filter_mem(pair(val, false), t, engaged_cell);
          mem_map(pair(val, false), filter(engaged_cell, t), fst);
        } else {
          two_indexes_into_engaged_nondistinct(t, i1 - 1, i2 - 1);
        }
      }
  }
}
@*/

/*@
lemma void erase_addresses_nonmem(dyn_entry e, list<dyn_entry> entries, list<ether_addri> addrs)
requires false == mem(get_dyn_addr(e), addrs);
ensures erase_addresses(cons(e, entries), addrs) == cons(e, erase_addresses(entries, addrs));
{
  switch(addrs) {
    case nil:
    case cons(h,t):
      erase_addresses_nonmem(e, entries, t);
      switch(e) { case dyn_entry(e_addr, e_port, e_time): }
  }
}
@*/

/*@

lemma void bridge_expire_erase_abstract(list<pair<ether_addri, uint32_t> > dyn_map,
                                        list<pair<uint16_t, bool> > vals,
                                        list<pair<ether_addri, bool> > keys,
                                        dchain indices,
                                        time_t time)
requires true == distinct(dchain_indexes_fp(indices)) &*&
         true == forall(dyn_map, (synced_pair)(keys)) &*&
         true == distinct(map(fst, filter(engaged_cell, keys))) &*&
         true == subset(map(snd, dyn_map), dchain_indexes_fp(indices)) &*&
         true == forall(dchain_get_expired_indexes_fp(indices, time),
                        (bounded)(length(keys))) &*&
         true == forall(dchain_get_expired_indexes_fp(indices, time),
                        (sup)(engaged_cell, (nth2)(keys)));
ensures multiset_eq(erase_addresses(gen_dyn_entries(dyn_map, vals, indices),
                                    vector_get_values_fp(keys, dchain_get_expired_indexes_fp(indices, time))),
                    expire_addresses(gen_dyn_entries(dyn_map, vals, indices),
                                     time)) == true;
{
  switch(dyn_map) {
    case nil:
      erase_addresses_nil(vector_get_values_fp(keys, dchain_get_expired_indexes_fp(indices, time)));
    case cons(h,t): switch(h) { case pair(addr, idx):
      bridge_expire_erase_abstract(t, vals, keys, indices, time);
      list<uint32_t> expired_i = dchain_get_expired_indexes_fp(indices, time);
      list<ether_addri> expired_e = vector_get_values_fp(keys, expired_i);
      assert gen_dyn_entries(dyn_map, vals, indices) ==
              cons(dyn_entry(addr, fst(nth(idx, vals)), dchain_get_time_fp(indices, idx)),
                   gen_dyn_entries(t, vals, indices));
      subset_mem_trans(map(snd, dyn_map), dchain_indexes_fp(indices), idx);
      dchain_indexes_contain_index(indices, idx);
      dchain_expired_in_expired(indices, idx, time);
      if (dchain_get_time_fp(indices, idx) < time) {
        assert true == mem(idx, expired_i);
        assert fst(nth(idx, keys)) == addr;
        vector_get_values_known(keys, expired_i, idx);
        assert true == mem(addr, expired_e);
        erase_addresses_known(dyn_entry(addr, fst(nth(idx, vals)), dchain_get_time_fp(indices, idx)),
                              gen_dyn_entries(t, vals, indices),
                              expired_e);
        assert erase_addresses(gen_dyn_entries(dyn_map, vals, indices),
                                expired_e) ==
              erase_addresses(gen_dyn_entries(t, vals, indices), expired_e);
        assert expire_addresses(gen_dyn_entries(dyn_map, vals, indices), time) ==
              expire_addresses(gen_dyn_entries(t, vals, indices), time);
      } else {
        assert false == mem(idx, expired_i);
        if (mem(addr, expired_e)) {
          int addr_index = index_of(addr, expired_e);
          int addr_idx = nth(addr_index, expired_i);
          map_preserves_length((sup)(fst, (nth2)(keys)), expired_i);
          assert fst(nth(idx, keys)) == addr;
          vector_get_values_index_of(keys, expired_i, addr);
          assert fst(nth(addr_idx, keys)) == addr;
          forall_nth(expired_i, (bounded)(length(keys)), addr_index);
          forall_nth(expired_i, (sup)(engaged_cell, (nth2)(keys)), addr_index);
          assert true == engaged_cell(nth(idx, keys));
          assert true == engaged_cell(nth(addr_idx, keys));
          two_indexes_into_engaged_nondistinct(keys, addr_idx, idx);
        }
        assert false == mem(addr, expired_e);

        erase_addresses_nonmem(dyn_entry(addr, fst(nth(idx, vals)), dchain_get_time_fp(indices, idx)),
                               gen_dyn_entries(t, vals, indices),
                               expired_e);
        assert erase_addresses(gen_dyn_entries(dyn_map, vals, indices),
                               expired_e) ==
               cons(dyn_entry(addr, fst(nth(idx, vals)), dchain_get_time_fp(indices, idx)),
                    erase_addresses(gen_dyn_entries(t, vals, indices),
                                    expired_e));
        assert expire_addresses(gen_dyn_entries(dyn_map, vals, indices), time) ==
               cons(dyn_entry(addr, fst(nth(idx, vals)), dchain_get_time_fp(indices, idx)),
                    expire_addresses(gen_dyn_entries(t, vals, indices), time));
        multiset_eq_cons_both(erase_addresses(gen_dyn_entries(t, vals, indices), expired_e),
                              expire_addresses(gen_dyn_entries(t, vals, indices), time),
                              dyn_entry(addr, fst(nth(idx, vals)), dchain_get_time_fp(indices, idx)));
      }
    }
  }
}
@*/

/*@
lemma void dchain_erase_all_expired_indexes(dchain ch, time_t time)
requires true;
ensures dchain_erase_indexes_fp(ch, dchain_get_expired_indexes_fp(ch, time)) == dchain_expire_old_indexes_fp(ch, time);
{
  switch(ch) { case dchain(alist, x1, x2, x3):}
}
@*/

/*@
lemma void map_erase_all_nil<kt,vt>(list<kt> keys)
requires true;
ensures map_erase_all_fp(nil, keys) == nil;
{
  switch(keys) {
    case nil:
    case cons(h,t):
      map_erase_all_nil(t);
  }
}
@*/

/*@
lemma void dchain_erase_another_one_keeps_time(dchain ch, list<int> e_indices, int e_ind, int index)
requires e_ind != index;
ensures dchain_get_time_fp(dchain_erase_indexes_fp(ch, cons(e_ind, e_indices)), index) ==
        dchain_get_time_fp(dchain_erase_indexes_fp(ch, e_indices), index);
{
  assume(false);//TODO
}
@*/

/*@
lemma void dchain_erase_idx_same_gen_entries(list<pair<ether_addri, uint32_t> > dyn_map,
                                             list<pair<uint16_t, bool> > vals,
                                             dchain ch,
                                             uint32_t idx,
                                             list<uint32_t> indices)
requires false == mem(idx, map(snd, dyn_map));
ensures gen_dyn_entries(dyn_map, vals, dchain_erase_indexes_fp(ch, indices)) ==
        gen_dyn_entries(dyn_map, vals, dchain_erase_indexes_fp(ch, cons(idx, indices)));
{
  switch(dyn_map) {
    case nil:
    case cons(h,t):
      switch(h) { case pair(addr, index):
        dchain_erase_another_one_keeps_time(ch, indices, idx, index);
        dchain_erase_idx_same_gen_entries(t, vals, ch, idx, indices);
      }
  }
}
@*/

/*@
lemma void map_erase_all_cons<kt,vt>(kt k, vt v, list<pair<kt,vt> > m, list<kt> keys)
requires false == mem(k, keys);
ensures map_erase_all_fp(cons(pair(k, v), m), keys) ==
        cons(pair(k, v), map_erase_all_fp(m, keys));
{
  switch(keys) {
    case nil:
    case cons(h,t):
      map_erase_all_cons(k, v, m, t);
  }
}
@*/

/*@
lemma void map_erase_one_more<kt,vt>(kt k, vt v, list<pair<kt,vt> > m, list<kt> keys)
requires false == mem(k, keys);
ensures map_erase_all_fp(cons(pair(k, v), m), cons(k, keys)) ==
        map_erase_all_fp(m, keys);
{
  assert map_erase_all_fp(cons(pair(k, v), m), cons(k, keys)) ==
         map_erase_fp(map_erase_all_fp(cons(pair(k, v), m), keys), k);
  map_erase_all_cons(k, v, m, keys);
  assert map_erase_fp(map_erase_all_fp(cons(pair(k, v), m), keys), k) ==
         map_erase_fp(cons(pair(k, v), map_erase_all_fp(m, keys)), k);
}
@*/

/*@
lemma void map_erase_preserves_nonmem_val<kt,vt>(list<pair<kt,vt> > m, vt v, kt k)
requires false == mem(v, map(snd, m));
ensures false == mem(v, map(snd, map_erase_fp(m, k)));
{
  switch(m) {
    case nil:
    case cons(h,t): switch(h) { case pair(aaa,bbb): }
      map_erase_preserves_nonmem_val(t, v, k);
  }
}

lemma void map_erase_all_preserves_nonmem_val<kt,vt>(list<pair<kt,vt> > m, vt v, list<kt> ks)
requires false == mem(v, map(snd, m));
ensures false == mem(v, map(snd, map_erase_all_fp(m, ks)));
{
  switch(ks) {
    case nil:
    case cons(h,t):
      map_erase_all_preserves_nonmem_val(m, v, t);
      map_erase_preserves_nonmem_val(map_erase_all_fp(m, t), v, h);
  }
}
@*/

/*@
lemma void map_erase_preserves_nonmem_key<kt,vt>(list<pair<kt,vt> > m, kt k, kt k_to_erase)
requires false == mem(k, map(fst, m));
ensures false == mem(k, map(fst, map_erase_fp(m, k_to_erase)));
{
  switch(m) {
    case nil:
    case cons(h,t): switch(h) { case pair(aaa,bbb): }
      map_erase_preserves_nonmem_key(t, k, k_to_erase);
  }
}

lemma void map_erase_all_preserves_nonmem_key<kt,vt>(list<pair<kt,vt> > m, kt k, list<kt> ks)
requires false == mem(k, map(fst, m));
ensures false == mem(k, map(fst, map_erase_all_fp(m, ks)));
{
  switch(ks) {
    case nil:
    case cons(h,t):
      map_erase_all_preserves_nonmem_key(m, k, t);
      map_erase_preserves_nonmem_key(map_erase_all_fp(m, t), k, h);
  }
}
@*/

/*@
lemma void synced_pairs_map_get(list<pair<ether_addri, bool> > keys,
                                list<pair<ether_addri, uint32_t> > m,
                                uint32_t v)
requires true == forall(m, (synced_pair)(keys)) &*&
         true == distinct(map(fst, filter(engaged_cell, keys))) &*&
         true == engaged_cell(nth(v, keys)) &*&
         true == map_has_fp(m, fst(nth(v, keys))) &*&
         0 <= v &*& v < length(keys);
ensures map_get_fp(m, fst(nth(v, keys))) == v;
{
  switch(m) {
    case nil:
    case cons(h,t):
      switch(h) { case pair(addr, index):
        if (index != v) {
          if (addr == fst(nth(v, keys))) {
            two_indexes_into_engaged_nondistinct(keys, index, v);
          }
          synced_pairs_map_get(keys, t, v);
        }
      }
  }
}
@*/

/*@
lemma void map_erase_val_nonmem<kt,vt>(list<pair<kt, vt> > m, kt k, vt v)
requires true == map_has_fp(m, k) &*&
         map_get_fp(m, k) == v &*&
         true == distinct(map(snd, m));
ensures false == mem(v, map(snd, map_erase_fp(m, k)));
{
  switch(m) {
    case nil:
    case cons(h,t):
      switch(h) { case pair(key,value):
        if (key != k) {
          map_erase_val_nonmem(t, k, v);
          if (value == v) {
            map_has_two_values_nondistinct(m, key, k);
          }
        }
      }
  }
}

lemma void map_erase_preserves_distinct_vals<kt,vt>(list<pair<kt,vt> > m, kt k)
requires true == distinct(map(snd, m));
ensures true == distinct(map(snd, map_erase_fp(m, k)));
{
  switch(m) {
    case nil:
    case cons(h,t): switch(h) { case pair(key, value):
      if (key != k) {
        map_erase_preserves_distinct_vals(t, k);
        map_erase_preserves_nonmem_val(t, value, k);
      }
    }
  }
}

lemma void map_erase_unrelevant_keep_kv<kt,vt>(list<pair<kt,vt> > m, kt k, vt v, kt k_to_erase)
requires k != k_to_erase &*&
         true == map_has_fp(m, k) &*&
         map_get_fp(m, k) == v &*&
         true == distinct(map(snd, m));
ensures true == map_has_fp(map_erase_fp(m, k_to_erase), k) &*&
        map_get_fp(map_erase_fp(m, k_to_erase), k) == v &*&
        true == distinct(map(snd, map_erase_fp(m, k_to_erase)));
{
  switch(m) {
    case nil:
    case cons(h,t): switch(h) { case pair(key, value):
      if (key == k) {
        map_erase_preserves_distinct_vals(t, k_to_erase);
        map_erase_preserves_nonmem_val(t, value, k_to_erase);
      } else if (key == k_to_erase) {
        return;
      } else {
        map_erase_unrelevant_keep_kv(t, k, v, k_to_erase);
        map_erase_preserves_nonmem_val(t, value, k_to_erase);
      }
    }
  }
}

lemma void map_erase_all_unrelevant_keep_kv<kt,vt>(list<pair<kt,vt> > m, kt k, vt v, list<kt> keys)
requires false == mem(k, keys) &*&
         true == map_has_fp(m, k) &*&
         map_get_fp(m, k) == v &*&
         true == distinct(map(snd, m));
ensures true == map_has_fp(map_erase_all_fp(m, keys), k) &*&
        map_get_fp(map_erase_all_fp(m, keys), k) == v &*&
        true == distinct(map(snd, map_erase_all_fp(m, keys)));
{
  switch(keys) {
    case nil:
    case cons(h,t):
      map_erase_all_unrelevant_keep_kv(m, k, v, t);
      map_erase_unrelevant_keep_kv(map_erase_all_fp(m, t), k, v, h);
  }
}

lemma void map_erase_all_nonmem<kt,vt>(list<pair<kt,vt> > m, kt k, vt v, list<kt> keys)
requires true == map_has_fp(m, k) &*&
         map_get_fp(m, k) == v &*&
         true == mem(k, keys) &*&
         true == distinct(map(snd, m));
ensures false == mem(v, map(snd, map_erase_all_fp(m, keys)));
{
  switch(keys) {
    case nil:
    case cons(h,t):
      if (!mem(k, t)) {
        assert map_get_fp(m, k) == v;
        map_erase_all_unrelevant_keep_kv(m, k, v, t);
        map_erase_val_nonmem(map_erase_all_fp(m, t), k, v);
      } else {
        map_erase_all_nonmem(m, k, v, t);
        map_erase_preserves_nonmem_val(map_erase_all_fp(m, t), v, h);
      }
  }
}
@*/

/*@
lemma void synced_pairs_map_has_key_for_idx(list<pair<ether_addri, uint32_t> > m,
                                            list<pair<ether_addri, bool> > v,
                                            int idx)
requires true == forall(m, (synced_pair)(v)) &*&
         true == mem(idx, map(snd, m));
ensures true == map_has_fp(m, fst(nth(idx, v)));
{
  switch(m) {
    case nil:
    case cons(h,t):
      switch(h) { case pair(key, index):
        if (index != idx)
          synced_pairs_map_has_key_for_idx(t, v, idx);
      }
  }
}
@*/

/*@
fixpoint bool bounded(int bound, int x) {
  return 0 <= x && x < bound;
}
@*/

/*@
lemma void map_erase_all_erase_head<kt,vt>(list<pair<kt,vt> > m, list<kt> keys, kt k, vt v)
requires true == mem(k, keys);
ensures map_erase_all_fp(cons(pair(k, v), m), keys) == map_erase_all_fp(m, keys);
{
  assume(false);//TODO
}
@*/

/*@
lemma void erase_one_address_after(list<pair<ether_addri, uint32_t> > dyn_map,
                                      list<pair<uint16_t, bool> > vals,
                                      list<pair<ether_addri, bool> > keys,
                                      dchain ch,
                                      uint32_t idx,
                                      list<uint32_t> indices)
requires true == forall(dyn_map, (synced_pair)(keys)) &*&
         true == distinct(map(snd, dyn_map)) &*&
         true == distinct(map(fst, dyn_map)) &*&
         true == distinct(map(fst, filter(engaged_cell, keys))) &*&
         true == distinct(cons(idx, indices)) &*&
         true == forall(cons(idx, indices), (bounded)(length(keys))) &*&
         true == forall(cons(idx, indices), (sup)(engaged_cell, (nth2)(keys)));
ensures multiset_eq(gen_dyn_entries(map_erase_all_fp
                                      (dyn_map,
                                       vector_get_values_fp(keys, cons(idx, indices))),
                                      vals,
                                      dchain_erase_indexes_fp(ch, cons(idx, indices))),
                    erase_address(gen_dyn_entries(map_erase_all_fp
                                      (dyn_map,
                                       vector_get_values_fp(keys, indices)),
                                      vals,
                                      dchain_erase_indexes_fp(ch, indices)),
                                  fst(nth(idx, keys)))) == true;
{
  switch(dyn_map) {
    case nil:
      map_erase_all_nil<ether_addri, uint32_t>(vector_get_values_fp(keys, cons(idx, indices)));
      map_erase_all_nil<ether_addri, uint32_t>(vector_get_values_fp(keys, indices));
    case cons(h,t):
      switch(h) {
        case pair(addr, index):
          ether_addri key_to_erase = fst(nth(idx, keys));
          assert map_erase_all_fp(dyn_map, vector_get_values_fp(keys, cons(idx, indices))) ==
                 map_erase_fp(map_erase_all_fp(dyn_map, vector_get_values_fp(keys, indices)), key_to_erase);
          if (key_to_erase == addr) {
            if (mem(addr, vector_get_values_fp(keys, indices))) {
              vector_get_values_index_of(keys, indices, addr);
              int other_idx_idx = index_of(addr, vector_get_values_fp(keys, indices));
              map_preserves_length((sup)(fst, (nth2)(keys)), indices);
              assert length(vector_get_values_fp(keys, indices)) == length(indices);
              assert 0 <= other_idx_idx &*& other_idx_idx < length(indices);
              int other_idx = nth(other_idx_idx, indices);
              assert true == mem(other_idx, indices);
              assert false == mem(idx, indices);
              forall_nth(indices, (bounded)(length(keys)), other_idx_idx);
              forall_nth(indices, (sup)(engaged_cell, (nth2)(keys)), other_idx_idx);
              assert fst(nth(idx, keys)) == addr;
              assert fst(nth(other_idx, keys)) == addr;
              two_indexes_into_engaged_nondistinct(keys, other_idx, idx);
              assert nth(other_idx, keys) == pair(addr, false);
              assert nth(idx, keys) == pair(addr, false);
              assert false;
            }
            assert vector_get_values_fp(keys, cons(idx, indices)) == cons(addr, vector_get_values_fp(keys, indices));
            map_erase_one_more(addr, index, t, vector_get_values_fp(keys, indices));
            assert(map_erase_all_fp(dyn_map, vector_get_values_fp(keys, cons(idx, indices))) ==
                   map_erase_all_fp(t, vector_get_values_fp(keys, indices)));//TODO
            assert gen_dyn_entries(map_erase_all_fp
                                      (dyn_map,
                                       vector_get_values_fp(keys, cons(idx, indices))),
                                      vals,
                                      dchain_erase_indexes_fp(ch, cons(idx, indices))) ==
                   gen_dyn_entries(map_erase_all_fp(t, vector_get_values_fp(keys, indices)),
                                   vals,
                                   dchain_erase_indexes_fp(ch, cons(idx, indices)));
            if (index != idx) {
              assert snd(nth(index, keys)) == false;
              assert fst(nth(index, keys)) == addr;
              assert fst(nth(idx, keys)) == addr;
              assert snd(nth(idx, keys)) == false;
              two_indexes_into_engaged_nondistinct(keys, idx, index);
              assert false == distinct(map(fst, filter(engaged_cell, keys)));
              assert false;
            }
            assert index == idx;
            assert false == mem(index, map(snd, t));
            map_erase_all_preserves_nonmem_val(t, idx, vector_get_values_fp(keys, indices));
            dchain_erase_idx_same_gen_entries(map_erase_all_fp(t, vector_get_values_fp(keys, indices)),
                                               vals, ch, idx, indices);
            assert gen_dyn_entries(map_erase_all_fp
                                      (dyn_map,
                                       vector_get_values_fp(keys, cons(idx, indices))),
                                      vals,
                                      dchain_erase_indexes_fp(ch, cons(idx, indices))) ==
                   gen_dyn_entries(map_erase_all_fp(t, vector_get_values_fp(keys, indices)),
                                   vals,
                                   dchain_erase_indexes_fp(ch, indices));
            map_erase_all_cons(addr, index, t, vector_get_values_fp(keys, indices));
            assert gen_dyn_entries(map_erase_all_fp
                                      (dyn_map,
                                       vector_get_values_fp(keys, indices)),
                                      vals,
                                      dchain_erase_indexes_fp(ch, indices)) ==
                   cons(dyn_entry(addr, fst(nth(index, vals)), dchain_get_time_fp(dchain_erase_indexes_fp(ch, indices), index)),
                        gen_dyn_entries(map_erase_all_fp(t, vector_get_values_fp(keys, indices)),
                                        vals,
                                        dchain_erase_indexes_fp(ch, indices)));
            assert addr == key_to_erase;
            multiset_eq_refl(gen_dyn_entries(map_erase_all_fp
                                      (dyn_map,
                                       vector_get_values_fp(keys, cons(idx, indices))),
                                      vals,
                                      dchain_erase_indexes_fp(ch, cons(idx, indices))));

            assert false == mem(fst(nth(idx, keys)), map(fst, t));
            map_erase_all_preserves_nonmem_key(t, fst(nth(idx, keys)), vector_get_values_fp(keys, indices));
            map_no_addr_gen_dyn_entries_no_addr(map_erase_all_fp
                                      (t,
                                       vector_get_values_fp(keys, indices)), vals, dchain_erase_indexes_fp(ch, indices), fst(nth(idx, keys)));
            erase_non_existent_address(gen_dyn_entries(map_erase_all_fp
                                      (t,
                                       vector_get_values_fp(keys, indices)),
                                      vals,
                                      dchain_erase_indexes_fp(ch, indices)),
                                      fst(nth(idx, keys)));
            assert erase_address(
                   gen_dyn_entries(map_erase_all_fp
                                      (t,
                                       vector_get_values_fp(keys, indices)),
                                      vals,
                                      dchain_erase_indexes_fp(ch, indices)),
                                fst(nth(idx, keys))) ==
                   gen_dyn_entries(map_erase_all_fp
                                      (t,
                                       vector_get_values_fp(keys, indices)),
                                      vals,
                                      dchain_erase_indexes_fp(ch, indices));

            assert erase_address(gen_dyn_entries(map_erase_all_fp
                                      (dyn_map,
                                       vector_get_values_fp(keys, indices)),
                                      vals,
                                      dchain_erase_indexes_fp(ch, indices)),
                                  fst(nth(idx, keys))) ==
                   gen_dyn_entries(map_erase_all_fp
                                      (t,
                                       vector_get_values_fp(keys, indices)),
                                      vals,
                                      dchain_erase_indexes_fp(ch, indices));
          } else {

            erase_one_address_after(t, vals, keys, ch, idx, indices);
            assert multiset_eq(gen_dyn_entries(map_erase_all_fp
                                            (t,
                                            vector_get_values_fp(keys, cons(idx, indices))),
                                            vals,
                                            dchain_erase_indexes_fp(ch, cons(idx, indices))),
                          erase_address(gen_dyn_entries(map_erase_all_fp
                                            (t,
                                            vector_get_values_fp(keys, indices)),
                                            vals,
                                            dchain_erase_indexes_fp(ch, indices)),
                                        fst(nth(idx, keys)))) == true;
            assert addr != key_to_erase;
            if (mem(addr, vector_get_values_fp(keys, indices))) {
              map_erase_all_erase_head(t, vector_get_values_fp(keys, cons(idx, indices)), addr, index);
              map_erase_all_erase_head(t, vector_get_values_fp(keys, indices), addr, index);
              return;
            }
            map_erase_all_cons(addr, index, t, vector_get_values_fp(keys, cons(idx, indices)));
            map_erase_all_cons(addr, index, t, vector_get_values_fp(keys, indices));
            assert gen_dyn_entries(map_erase_all_fp(dyn_map, vector_get_values_fp(keys, cons(idx, indices))), vals,
                                   dchain_erase_indexes_fp(ch, cons(idx, indices))) ==
                   cons(dyn_entry(addr, fst(nth(index, vals)), dchain_get_time_fp(dchain_erase_indexes_fp(ch, cons(idx, indices)), index)),
                    gen_dyn_entries(map_erase_all_fp(t, vector_get_values_fp(keys, cons(idx, indices))), vals,
                                   dchain_erase_indexes_fp(ch, cons(idx, indices))));
            if (idx == index) {
              assert fst(nth(index, keys)) == addr;
              assert fst(nth(idx, keys)) == key_to_erase;
              assert addr != key_to_erase;
              assert false;
            }
            dchain_erase_another_one_keeps_time(ch, indices, idx, index);
            assert(true == distinct(map(snd, t)));
            if (map_has_fp(t, fst(nth(idx, keys)))) {
              synced_pairs_map_get(keys, t, idx);
            }
            if (false == map_has_fp(t, fst(nth(idx, keys)))) {
              if (mem(idx, map(snd, t))) {
                synced_pairs_map_has_key_for_idx(t, keys, idx);
                assert false;
              }
              assert false == mem(idx, map(snd, t));
              map_erase_all_preserves_nonmem_val(t, idx, vector_get_values_fp(keys, cons(idx, indices)));
            } else {
              map_erase_all_nonmem(t, fst(nth(idx, keys)), idx, vector_get_values_fp(keys, cons(idx, indices)));
            }
            dchain_erase_idx_same_gen_entries(map_erase_all_fp(t, vector_get_values_fp(keys, cons(idx, indices))),
                                               vals, ch, idx, indices);
            assert gen_dyn_entries(map_erase_all_fp(dyn_map, vector_get_values_fp(keys, cons(idx, indices))), vals,
                                   dchain_erase_indexes_fp(ch, cons(idx, indices))) ==
                   cons(dyn_entry(addr, fst(nth(index, vals)), dchain_get_time_fp(dchain_erase_indexes_fp(ch, indices), index)),
                    gen_dyn_entries(map_erase_all_fp(t, vector_get_values_fp(keys, cons(idx, indices))), vals,
                                   dchain_erase_indexes_fp(ch, indices)));

            assert map_erase_all_fp(dyn_map, vector_get_values_fp(keys, indices)) ==
                   cons(h, map_erase_all_fp(t, vector_get_values_fp(keys, indices)));
            assert gen_dyn_entries(map_erase_all_fp(dyn_map, vector_get_values_fp(keys, indices)),
                                   vals,
                                   dchain_erase_indexes_fp(ch, indices)) ==
                   cons(dyn_entry(addr,
                                  fst(nth(index, vals)),
                                  dchain_get_time_fp(dchain_erase_indexes_fp(ch, indices), index)),
                        gen_dyn_entries(map_erase_all_fp(t, vector_get_values_fp(keys, indices)), vals, dchain_erase_indexes_fp(ch, indices)));

            assert erase_address(gen_dyn_entries(map_erase_all_fp
                                      (dyn_map,
                                       vector_get_values_fp(keys, indices)),
                                      vals,
                                      dchain_erase_indexes_fp(ch, indices)),
                                  fst(nth(idx, keys))) ==
                   cons(dyn_entry(addr, fst(nth(index, vals)), dchain_get_time_fp(dchain_erase_indexes_fp(ch, indices), index)),
                        erase_address(gen_dyn_entries(map_erase_all_fp
                                       (t, vector_get_values_fp(keys, indices)),
                                       vals,
                                       dchain_erase_indexes_fp(ch, indices)),
                                      fst(nth(idx, keys))));

            assert gen_dyn_entries(map_erase_all_fp(dyn_map, vector_get_values_fp(keys, cons(idx, indices))), vals,
                                   dchain_erase_indexes_fp(ch, cons(idx, indices))) ==
                   cons(dyn_entry(addr, fst(nth(index, vals)), dchain_get_time_fp(dchain_erase_indexes_fp(ch, indices), index)),
                    gen_dyn_entries(map_erase_all_fp(t, vector_get_values_fp(keys, cons(idx, indices))), vals,
                                   dchain_erase_indexes_fp(ch, indices)));

          }
      }
  }
}
@*/

/*@
lemma void erase_address_still_mset_eq(list<dyn_entry> table1, list<dyn_entry> table2, ether_addri addr)
requires true == multiset_eq(table1, table2) &*&
         true == distinct(map(get_dyn_addr, table2));
ensures true == multiset_eq(erase_address(table1, addr), erase_address(table2, addr)) &*&
        true == distinct(map(get_dyn_addr, erase_address(table2, addr)));
{
  assume(false);//TODO
}
@*/

/*@
lemma void dyn_addresses_distinct(list<pair<ether_addri, uint32_t> > dyn_map,
                                      list<pair<uint16_t, bool> > vals,
                                      list<pair<ether_addri, bool> > keys,
                                      dchain ch)
requires map_vec_chain_coherent(dyn_map, keys, ch);
ensures map_vec_chain_coherent(dyn_map, keys, ch) &*&
        true == distinct(map(get_dyn_addr, gen_dyn_entries(dyn_map, vals, ch)));
{
  assume(false);//TODO
}
@*/

/*@
lemma void dchain_erase_indexes_nil(dchain ch)
requires true;
ensures dchain_erase_indexes_fp(ch, nil) == ch;
{
  assume(false);//TODO
}
@*/

/*@
lemma void bridge_erase_many_abstract(list<pair<ether_addri, uint32_t> > dyn_map,
                                      list<pair<uint16_t, bool> > vals,
                                      list<pair<ether_addri, bool> > keys,
                                      dchain ch,
                                      list<uint32_t> exp_indices)
requires map_vec_chain_coherent(dyn_map, keys, ch) &*&
         true == distinct(exp_indices) &*&
         true == forall(exp_indices, (bounded)(length(keys))) &*&
         true == forall(exp_indices, (sup)(engaged_cell, (nth2)(keys)));
ensures map_vec_chain_coherent(dyn_map, keys, ch) &*&
        true == distinct(map(get_dyn_addr,
                             erase_addresses(gen_dyn_entries(dyn_map, vals, ch),
                                             vector_get_values_fp(keys, exp_indices)))) &*&
        multiset_eq(gen_dyn_entries(map_erase_all_fp
                                      (dyn_map,
                                       vector_get_values_fp(keys, exp_indices)),
                                      vals,
                                      dchain_erase_indexes_fp(ch, exp_indices)),
                    erase_addresses(gen_dyn_entries(dyn_map, vals, ch),
                                    vector_get_values_fp(keys, exp_indices))) == true;
{
  switch(exp_indices) {
    case nil:
      dyn_addresses_distinct(dyn_map, vals, keys, ch);
      multiset_eq_refl(gen_dyn_entries(dyn_map, vals, ch));
      dchain_erase_indexes_nil(ch);
    case cons(h,t):
      bridge_erase_many_abstract(dyn_map, vals, keys, ch, t);
      list<ether_addri> exp_addrs_t = vector_get_values_fp(keys, t);

      assert erase_address(erase_addresses(gen_dyn_entries(dyn_map, vals, ch), vector_get_values_fp(keys, t)), fst(nth(h, keys))) ==
              erase_addresses(gen_dyn_entries(dyn_map, vals, ch), vector_get_values_fp(keys, exp_indices));

      mvc_coherent_keys_synced(dyn_map, keys, ch);
      mvc_coherent_distinct(dyn_map, keys, ch);
      erase_one_address_after(dyn_map, vals, keys, ch, h, t);
      assert multiset_eq(gen_dyn_entries(map_erase_all_fp
                                    (dyn_map,
                                      vector_get_values_fp(keys, exp_indices)),
                                    vals,
                                    dchain_erase_indexes_fp(ch, exp_indices)),
                  erase_address(gen_dyn_entries(map_erase_all_fp
                                    (dyn_map,
                                      vector_get_values_fp(keys, t)),
                                    vals,
                                    dchain_erase_indexes_fp(ch, t)),
                                fst(nth(h, keys)))) == true;

      bridge_erase_many_abstract(dyn_map, vals, keys, ch, t);
      assert true == distinct(map(get_dyn_addr, erase_addresses(gen_dyn_entries(dyn_map, vals, ch), vector_get_values_fp(keys, t))));

      assert multiset_eq(gen_dyn_entries(map_erase_all_fp
                                    (dyn_map,
                                      vector_get_values_fp(keys, t)),
                                    vals,
                                    dchain_erase_indexes_fp(ch, t)),
                  erase_addresses(gen_dyn_entries(dyn_map, vals, ch),
                                  vector_get_values_fp(keys, t))) == true;

      erase_address_still_mset_eq(gen_dyn_entries(map_erase_all_fp
                                    (dyn_map,
                                      vector_get_values_fp(keys, t)),
                                    vals,
                                    dchain_erase_indexes_fp(ch, t)),
                                  erase_addresses(gen_dyn_entries(dyn_map, vals, ch),
                                                  vector_get_values_fp(keys, t)),
                                  fst(nth(h, keys)));
      assert multiset_eq(erase_address(gen_dyn_entries(map_erase_all_fp
                                    (dyn_map,
                                      vector_get_values_fp(keys, t)),
                                    vals,
                                    dchain_erase_indexes_fp(ch, t)),
                                    fst(nth(h, keys))),
                  erase_address(erase_addresses(gen_dyn_entries(dyn_map, vals, ch),
                                  vector_get_values_fp(keys, t)),
                                fst(nth(h, keys)))) == true;

      assert erase_address(erase_addresses(gen_dyn_entries(dyn_map, vals, ch), vector_get_values_fp(keys, t)), fst(nth(h, keys))) ==
              erase_addresses(gen_dyn_entries(dyn_map, vals, ch), vector_get_values_fp(keys, exp_indices));
      multiset_eq_trans(gen_dyn_entries(map_erase_all_fp
                                    (dyn_map,
                                      vector_get_values_fp(keys, exp_indices)),
                                    vals,
                                    dchain_erase_indexes_fp(ch, exp_indices)),
                        erase_address(gen_dyn_entries(map_erase_all_fp
                                    (dyn_map,
                                      vector_get_values_fp(keys, t)),
                                    vals,
                                    dchain_erase_indexes_fp(ch, t)),
                                fst(nth(h, keys))),
                        erase_addresses(gen_dyn_entries(dyn_map, vals, ch), vector_get_values_fp(keys, exp_indices)));
      assert true == distinct(map(get_dyn_addr, erase_addresses(gen_dyn_entries(dyn_map, vals, ch), vector_get_values_fp(keys, exp_indices))));

  }
}
@*/

/*@
lemma void mvc_coherent_expired_indexes<kt>(list<pair<kt, int> > m,
                                            list<pair<kt, bool> > v,
                                            dchain ch,
                                            time_t time)
requires map_vec_chain_coherent(m, v, ch);
ensures map_vec_chain_coherent(m, v, ch) &*&
        true == distinct(dchain_get_expired_indexes_fp(ch, time)) &*&
        true == forall(dchain_get_expired_indexes_fp(ch, time),
                       (bounded)(length(v))) &*&
        true == forall(dchain_get_expired_indexes_fp(ch, time),
                       (sup)(engaged_cell, (nth2)(v)));
{
  assume(false);//TODO
}
@*/


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
  mvc_coherent_distinct(dyn_map, keys, indices);
  mvc_coherent_keys_synced(dyn_map, keys, indices);
  msubset_subset(map(snd, dyn_map), dchain_indexes_fp(indices));
  mvc_coherent_expired_indexes(dyn_map, keys, indices, time);
  bridge_expire_erase_abstract(dyn_map, vals, keys, indices, time);
  bridge_erase_many_abstract(dyn_map, vals, keys, indices, dchain_get_expired_indexes_fp(indices, time));
  dchain_erase_all_expired_indexes(indices, time);
  multiset_eq_trans(gen_dyn_entries(map_erase_all_fp
                                    (dyn_map,
                                      vector_get_values_fp
                                        (keys, dchain_get_expired_indexes_fp
                                                (indices, time))),
                                    vals,
                                    dchain_expire_old_indexes_fp(indices, time)),
                    erase_addresses(gen_dyn_entries(dyn_map, vals, indices),
                                    vector_get_values_fp(keys, dchain_get_expired_indexes_fp(indices, time))),
                    expire_addresses(gen_dyn_entries(dyn_map, vals, indices),
                                     time));
  multiset_eq_set_eq(gen_dyn_entries(map_erase_all_fp
                                (dyn_map,
                                  vector_get_values_fp
                                    (keys, dchain_get_expired_indexes_fp
                                            (indices, time))),
                                vals,
                                dchain_expire_old_indexes_fp(indices, time)),
               expire_addresses(gen_dyn_entries(dyn_map, vals, indices),
                                time));
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
