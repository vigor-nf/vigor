#include "coherence.h"

/*@
  predicate dmap_dchain_coherent<t1,t2,vt>(dmap<t1,t2,vt> m, dchain ch) =
    dchain_index_range_fp(ch) == dmap_cap_fp(m) &*&
    true == subset(dchain_indexes_fp(ch), dmap_indexes_used_fp(m)) &*&
    true == subset(dmap_indexes_used_fp(m), dchain_indexes_fp(ch));
  @*/

/*@

lemma void coherent_same_indexes<t1,t2,vt>
             (dmap<t1,t2,vt> m, dchain ch)
requires dmap_dchain_coherent(m, ch);
ensures dmap_dchain_coherent(m, ch) &*&
        true == subset(dchain_indexes_fp(ch), dmap_indexes_used_fp(m)) &*&
        true == subset(dmap_indexes_used_fp(m), dchain_indexes_fp(ch));
{
  open dmap_dchain_coherent(m, ch);
  close dmap_dchain_coherent(m, ch);
}
@*/

/*@

lemma void empty_dmap_dchain_coherent<t1,t2,vt>(int len)
requires 0 <= len;
ensures dmap_dchain_coherent<t1,t2,vt>
         (empty_dmap_fp<t1,t2,vt>(len), empty_dchain_fp(len, 0));
{
  empty_dmap_cap<t1,t2,vt>(len);
  dmap_empty_no_indexes_used<t1,t2,vt>(len);
  close dmap_dchain_coherent(empty_dmap_fp<t1,t2,vt>(len),
                             empty_dchain_fp(len, 0));
}

lemma void coherent_dmap_used_dchain_allocated<t1,t2,vt>
             (dmap<t1,t2,vt> m, dchain ch, int idx)
requires dmap_dchain_coherent(m, ch) &*& dmap_index_used_fp(m, idx) == true;
ensures dmap_dchain_coherent(m, ch) &*&
        dchain_allocated_fp(ch, idx) == true;
{
  open dmap_dchain_coherent(m, ch);
  dmap_index_used_inbounds(m, idx);
  dmap_indexes_contain_index_used(m, idx);
  mem_subset(idx, dmap_indexes_used_fp(m), dchain_indexes_fp(ch));
  dchain_indexes_contain_index(ch, idx);
  close dmap_dchain_coherent(m, ch);
}

@*/

/*@
lemma void rejuvenate_preserves_coherent<t1,t2,vt>
             (dmap<t1,t2,vt> m, dchain ch,
              int index, time_t time)
requires dmap_dchain_coherent(m, ch) &*&
         true == dchain_allocated_fp(ch, index);
ensures dmap_dchain_coherent(m, dchain_rejuvenate_fp(ch, index, time));
{
  open dmap_dchain_coherent(m, ch);
  dchain_rejuvenate_preserves_indexes_set(ch, index, time);
  rejuvenate_preserves_index_range(ch, index, time);
  dchain nch = dchain_rejuvenate_fp(ch, index, time);
  subset_trans(dchain_indexes_fp(nch), dchain_indexes_fp(ch),
               dmap_indexes_used_fp(m));
  subset_trans(dmap_indexes_used_fp(m), dchain_indexes_fp(ch),
               dchain_indexes_fp(nch));
  close dmap_dchain_coherent(m, nch);
}
@*/

/*@
  lemma void dmap_put_equiv_indexes_sub<vt>(list<option<vt> > vals,
                                            int ind, vt v, int start)
  requires true;
  ensures true == subset(nonempty_indexes_fp(update(ind-start, some(v), vals),
                                             start),
                         cons(ind, nonempty_indexes_fp(vals, start)));
  {
    switch(vals) {
      case nil: return;
      case cons(h,t):
        if (start == ind) {
          switch(h) {
            case none: break;
            case some(lll):
              add_extra_preserves_subset(nonempty_indexes_fp(t, start+1),
                                         nonempty_indexes_fp(t, start+1), start);
          }
          add_extra_preserves_subset(nonempty_indexes_fp(t, start+1),
                                     nonempty_indexes_fp(vals, start), ind);
        } else {
          dmap_put_equiv_indexes_sub(t, ind, v, start+1);
          switch(h) {
            case none: break;
            case some(aaa):
              list<int> prev_idxes = nonempty_indexes_fp(t, start+1);
              add_extra_preserves_subset(prev_idxes, prev_idxes, start);
              add_extra_preserves_subset(prev_idxes, cons(start, prev_idxes),
                                         ind);

              subset_trans(nonempty_indexes_fp(update(ind-start-1, some(v), t),
                                               start+1),
                           cons(ind, nonempty_indexes_fp(t, start+1)),
                           cons(ind, nonempty_indexes_fp(vals, start)));
              break;
          }
        }
    }
  }
  @*/

/*@
  lemma void dmap_put_equiv_indexes_sup<vt>(list<option<vt> > vals,
                                            int ind, vt v, int start)
  requires true;
  ensures true == subset(nonempty_indexes_fp(vals, start),
                         nonempty_indexes_fp(update(ind-start, some(v), vals),
                                             start));
  {
    switch(vals) {
      case nil: return;
      case cons(h,t):
        dmap_put_equiv_indexes_sup(t, ind, v, start+1);
        if (ind == start) {
          add_extra_preserves_subset(nonempty_indexes_fp(t, start+1),
                                     nonempty_indexes_fp(t, start+1),
                                     start);
        }
        switch(h) {
          case none:
            return;
          case some(ignore):
            add_extra_preserves_subset(nonempty_indexes_fp(t, start+1),
                                       nonempty_indexes_fp(update(ind-start-1,
                                                                  some(v), t),
                                                           start+1),
                                       start);
            break;
        }
    }
  }
  @*/

/*@
  lemma void dmap_put_occupies<vt>(list<option<vt> > vals,
                                   int ind, vt v, int start)
  requires 0 <= start &*& start <= ind &*& ind - start < length(vals);
  ensures true == mem(ind, nonempty_indexes_fp(update(ind-start, some(v), vals),
                                               start));
  {
    switch(vals) {
      case nil: return;
      case cons(h,t):
        if (start == ind) return;
        dmap_put_occupies(t, ind, v, start+1);
        switch(h) {
          case none: break;
          case some(ignore): break;
        }
    }
  }
  @*/

/*@
  lemma void dmap_put_equiv_indexes<t1,t2,vt>(dmap<t1,t2,vt> m,
                                              int ind, vt value,
                                              fixpoint (vt,t1) vk1,
                                              fixpoint (vt,t2) vk2)
  requires 0 <= ind &*& ind < dmap_cap_fp(m);
  ensures true == subset(dmap_indexes_used_fp
                          (dmap_put_fp(m, ind, value, vk1, vk2)),
                         cons(ind, dmap_indexes_used_fp(m))) &*&
          true == subset(cons(ind, dmap_indexes_used_fp(m)),
                         dmap_indexes_used_fp
                          (dmap_put_fp(m, ind, value, vk1, vk2)));
  {
    switch(m) { case dmap(ma, mb, vals):
      dmap_put_equiv_indexes_sub(vals, ind, value, 0);
      dmap_put_equiv_indexes_sup(vals, ind, value, 0);
      dmap_put_occupies(vals, ind, value, 0);
    }
  }
  @*/

/*@
lemma void coherent_put_allocated_preserves_coherent<t1,t2,vt>
(dmap<t1,t2,vt> m, dchain ch, t1 k1, t2 k2,
 vt value, int ind, time_t t,
 fixpoint (vt,t1) vk1,
 fixpoint (vt,t2) vk2)
requires dmap_dchain_coherent(m, ch) &*&
         0 <= ind &*& ind < dmap_cap_fp(m);
ensures dmap_dchain_coherent(dmap_put_fp(m, ind, value, vk1, vk2),
                             dchain_allocate_fp(ch, ind, t));
{
  open dmap_dchain_coherent(m, ch);
  dchain_allocate_append_to_indexes(ch, ind, t);
  assert dchain_indexes_fp(dchain_allocate_fp(ch, ind, t)) ==
         append(dchain_indexes_fp(ch), cons(ind, nil));
  if (mem(ind, dmap_indexes_used_fp(m))) {
    subset_mem_trans(dmap_indexes_used_fp(m), dchain_indexes_fp(ch), ind);
  }
  dmap_put_equiv_indexes(m, ind, value, vk1, vk2);
  assert true == subset(dmap_indexes_used_fp(dmap_put_fp(m, ind, value,
                                                         vk1, vk2)),
                        cons(ind, dmap_indexes_used_fp(m)));
  assert true == subset(dmap_indexes_used_fp(m),
                        dmap_indexes_used_fp(dmap_put_fp(m, ind, value,
                                                         vk1, vk2)));

  dmap_put_preserves_cap(m, ind, value, vk1, vk2);
  allocate_preserves_index_range(ch, ind, t);
  subset_append2(dmap_indexes_used_fp(m), dchain_indexes_fp(ch),
                 cons(ind, nil));
  add_extra_preserves_subset(dchain_indexes_fp(ch),
                             dmap_indexes_used_fp(m), ind);
  subset_append(dchain_indexes_fp(ch), cons(ind, nil),
                cons(ind, dmap_indexes_used_fp(m)));
  subset_trans(dmap_indexes_used_fp(dmap_put_fp(m, ind, value, vk1, vk2)),
               cons(ind, dmap_indexes_used_fp(m)),
               dchain_indexes_fp(dchain_allocate_fp(ch, ind, t)));
  subset_trans(dchain_indexes_fp(dchain_allocate_fp(ch, ind, t)),
               cons(ind, dmap_indexes_used_fp(m)),
               dmap_indexes_used_fp(dmap_put_fp(m, ind, value, vk1, vk2)));
  close dmap_dchain_coherent(dmap_put_fp(m, ind, value, vk1, vk2),
                             dchain_allocate_fp(ch, ind, t));
}

@*/


/*@
  lemma void dchain_out_of_space_to_indexes_size(dchain ch)
  requires true;
  ensures dchain_out_of_space_fp(ch) ==
          (dchain_index_range_fp(ch) <= length(dchain_indexes_fp(ch)));
  {
    switch(ch) { case dchain(alist, index_range, lo, hi):
      map_effect_on_len(alist, fst);
    }
  }
  @*/

/*@

lemma void coherent_dchain_non_out_of_space_map_nonfull<t1,t2,vt>
            (dmap<t1,t2,vt> m, dchain ch)
requires dmappingp<t1,t2,vt>(m, ?a, ?b, ?c, ?d, ?e, ?g, ?h, ?i, ?j, ?k, ?l, ?n, ?f) &*&
         dmap_dchain_coherent(m, ch) &*&
         dchain_out_of_space_fp(ch) == false;
ensures dmappingp<t1,t2,vt>(m, a, b, c, d, e, g, h, i, j, k, l, n, f) &*&
        dmap_dchain_coherent(m, ch) &*&
        dmap_size_fp(m) < dmap_cap_fp(m);
{
  open dmap_dchain_coherent(m, ch);

  dmap_indexes_used_distinct(m);
  distinct_subset_sublen(dmap_indexes_used_fp(m), dchain_indexes_fp(ch));
  dchain_out_of_space_to_indexes_size(ch);
  dmap_size_of_indexes_used(m);

  close dmap_dchain_coherent(m, ch);
}

@*/

/*@
  lemma void coherent_expire_one<t1,t2,vt>(dmap<t1,t2,vt> m,
                                           dchain ch,
                                           int idx,
                                           fixpoint (vt,t1) vk1,
                                           fixpoint (vt,t2) vk2)
  requires dmap_dchain_coherent(m, ch) &*&
           dchain_nodups(ch) &*&
           true == dchain_allocated_fp(ch, idx) &*&
           0 <= idx;
  ensures dmap_dchain_coherent(dmap_erase_fp(m, idx, vk1, vk2),
                               dchain_remove_index_fp(ch, idx)) &*&
          dchain_nodups(dchain_remove_index_fp(ch, idx));
  {
    open dmap_dchain_coherent(m, ch);
    dmap<t1,t2,vt> nm = dmap_erase_fp(m, idx, vk1, vk2);
    dchain nch = dchain_remove_index_fp(ch, idx);
    dchain_remove_keeps_ir(ch, idx);
    dmap_erase_keeps_cap(m, idx, vk1, vk2);
    assert dchain_index_range_fp(nch) == dmap_cap_fp(nm);
    dchain_remove_idx_from_indexes(ch, idx);
    assert dchain_indexes_fp(nch) ==
           remove(idx, dchain_indexes_fp(ch));
    dmap_erase_removes_index(m, idx, vk1, vk2);
    assert dmap_indexes_used_fp(nm) ==
           remove(idx, dmap_indexes_used_fp(m));

    dchain_nodups_unique_idx(ch, idx);
    dmap_indexes_used_distinct(m);
    distinct_mem_remove(idx, dmap_indexes_used_fp(m));
    remove_both_subset(idx, dchain_indexes_fp(ch), dmap_indexes_used_fp(m));
    remove_both_subset(idx, dmap_indexes_used_fp(m), dchain_indexes_fp(ch));

    dchain_remove_keeps_nodups(ch, idx);

    close dmap_dchain_coherent(nm, nch);
  }
  @*/

/*@
  lemma void coherent_same_cap<t1,t2,vt>(dmap<t1,t2,vt> m, dchain ch)
  requires dmap_dchain_coherent(m, ch);
  ensures dmap_dchain_coherent(m, ch) &*&
          dmap_cap_fp(m) == dchain_index_range_fp(ch);
  {
    open dmap_dchain_coherent(m, ch);
    close dmap_dchain_coherent(m, ch);
  }
  @*/

/*@
  lemma void coherent_old_index_used<t1,t2,vt>(dmap<t1,t2,vt> m, dchain ch)
  requires dmap_dchain_coherent(m, ch) &*&
           false == dchain_is_empty_fp(ch) &*&
           0 <= dchain_get_oldest_index_fp(ch) &*&
           dchain_get_oldest_index_fp(ch) < dchain_index_range_fp(ch);
  ensures dmap_dchain_coherent(m, ch) &*&
          true == dmap_index_used_fp(m, dchain_get_oldest_index_fp(ch));
  {
    dchain_oldest_allocated(ch);
    coherent_same_cap(m, ch);
    open dmap_dchain_coherent(m, ch);
    dchain_indexes_contain_index(ch, dchain_get_oldest_index_fp(ch));
    mem_subset(dchain_get_oldest_index_fp(ch), dchain_indexes_fp(ch),
               dmap_indexes_used_fp(m));
    dmap_indexes_contain_index_used(m, dchain_get_oldest_index_fp(ch));
    close dmap_dchain_coherent(m, ch);
  }
  @*/

/*@
  lemma void kkeeper_erase_one_from_vec<t>(list<void*> addrs,
                                           list<pair<t, bool> > contents,
                                           list<pair<t, void*> > addr_map,
                                           int index)
  requires 0 <= index &*& index < length(contents) &*&
           true == forall2(contents, addrs, (kkeeper)(addr_map));
  ensures true == forall2(vector_erase_fp(contents, index), addrs,
                          (kkeeper)(addr_map));
  {
    switch(contents) {
      case nil: return;
      case cons(ch, ct):
        switch(addrs) {
          case nil: return;
          case cons(ah, at):
            if (index == 0) return;
            kkeeper_erase_one_from_vec(at, ct, addr_map, index - 1);
      }
    }
  }

  fixpoint bool owned_or_not_this<t>(t val, pair<t, bool> cell) {
    return snd(cell) || fst(cell) != val;
  }

  lemma void kkeeper_erase_one_from_map<t>(list<void*> addrs,
                                           list<pair<t, bool> > contents,
                                           list<pair<t, void*> > addr_map,
                                           t val)
  requires true == forall2(contents, addrs, (kkeeper)(addr_map)) &*&
           true == forall(contents, (owned_or_not_this)(val));
  ensures true == forall2(contents, addrs,
                          (kkeeper)(map_erase_fp(addr_map, val)));
  {
    switch(contents) {
      case nil: return;
      case cons(ch, ct):
        switch(addrs) {
          case nil: return;
          case cons(ah, at):
            if (!snd(ch)) {
              map_erase_keeps_others(addr_map, val, fst(ch));
            }
            kkeeper_erase_one_from_map(at, ct, addr_map, val);
      }
    }
  }

  lemma void kkeeper_nth_addrs_is_map_get<t>(list<void*> addrs,
                                             list<pair<t, bool> > contents,
                                             list<pair<t, void*> > addr_map,
                                             int index)
  requires 0 <= index &*& index < length(contents) &*&
           length(contents) <= length(addrs) &*&
           true == forall2(contents, addrs, (kkeeper)(addr_map)) &*&
           nth(index, contents) == pair(?val, false);
  ensures map_get_fp(addr_map, val) == nth(index, addrs);
  {
    switch(contents) {
      case nil: return;
      case cons(ch, ct):
        switch(addrs) {
          case nil: return;
          case cons(ah, at):
            if (index == 0) {
              return;
            }
            kkeeper_nth_addrs_is_map_get(at, ct, addr_map, index - 1);
        }
     }
  }

  lemma void kkeeper_non_mem_non_mem<t>(list<void*> addrs,
                                        list<pair<t, bool> > contents,
                                        list<pair<t, void*> > addr_map,
                                        t val)
  requires true == forall2(contents, addrs, (kkeeper)(addr_map)) &*&
           length(contents) <= length(addrs) &*&
           false == mem(map_get_fp(addr_map, val), addrs);
  ensures true == forall(contents, (owned_or_not_this)(val));
  {
    switch(contents) {
      case nil: return;
      case cons(ch, ct):
        switch(addrs) {
          case nil: return;
          case cons(ah, at):
            kkeeper_non_mem_non_mem(at, ct, addr_map, val);
      }
    }
  }

  lemma void kkeeper_no_dups_owned_or_not_this<t>(list<void*> addrs,
                                                  list<pair<t, bool> > contents,
                                                  list<pair<t, void*> > addr_map,
                                                  int index)
  requires 0 <= index &*& index < length(contents) &*&
           length(contents) <= length(addrs) &*&
           true == forall2(contents, addrs, (kkeeper)(addr_map)) &*&
           nth(index, contents) == pair(?val, false) &*&
           true == no_dups(addrs);
  ensures true == forall(vector_erase_fp(contents, index),
                         (owned_or_not_this)(val));
  {
    switch(contents) {
      case nil: return;
      case cons(ch, ct):
        switch(addrs) {
          case nil: return;
          case cons(ah, at):
            if (index == 0) {
              assert false == mem(ah, at);
              assert map_get_fp(addr_map, val) == ah;
              kkeeper_non_mem_non_mem(at, ct, addr_map, val);
              assert true == forall(ct, (owned_or_not_this)(val));
              return;
            }
            kkeeper_no_dups_owned_or_not_this(at, ct, addr_map, index - 1);
            if (!snd(ch)) {
              if (fst(ch) == fst(nth(index, contents))) {
                kkeeper_nth_addrs_is_map_get(addrs, contents, addr_map, index);
                assert ah == nth(index, addrs);
                assert true == mem(ah, addrs);
                assert false;
              }
            }
      }
    }
  }

  lemma void kkeeper_erase_one<t>(list<void*> addrs,
                                  list<pair<t, bool> > contents,
                                  list<pair<t, void*> > addr_map,
                                  int index)
  requires 0 <= index &*& index < length(contents) &*&
           length(contents) <= length(addrs) &*&
           true == forall2(contents, addrs, (kkeeper)(addr_map)) &*&
           nth(index, contents) == pair(?val, false) &*&
           true == no_dups(addrs);
  ensures true == forall2(vector_erase_fp(contents, index), addrs,
                          (kkeeper)(map_erase_fp(addr_map, val)));
  {
    kkeeper_erase_one_from_vec(addrs, contents, addr_map, index);
    nth_update(index, index, pair(val, true), contents);
    kkeeper_no_dups_owned_or_not_this(addrs, contents, addr_map, index);
    kkeeper_erase_one_from_map(addrs, vector_erase_fp(contents, index),
                               addr_map, val);
  }
  @*/

/*@
  lemma void empty_kkeeper<t>(list<void*> addrs,
                              list<pair<t, bool> > contents,
                              list<pair<t, void*> > addr_map,
                              int capacity)
  requires length(contents) == capacity &*&
           true == forall(contents, snd);
  ensures true == forall2(contents, addrs, (kkeeper)(addr_map));
  {
    switch(contents) {
      case nil: return;
      case cons(h1,t1):
        switch(addrs) {
          case nil: return;
            case cons(h2,t2):
              empty_kkeeper(t2, t1, addr_map, capacity - 1);
        }
    }
  }
  @*/

/*@
  fixpoint bool consistent_pair<kt>(list<pair<kt, int> > m,
                                    dchain ch,
                                    int idx, pair<kt, bool> el) {
    switch(el) {
      case pair(car, cdr):
        return cdr ?
          (false == dchain_allocated_fp(ch, idx))
          :
          (map_has_fp(m, car) &&
           map_get_fp(m, car) == idx &&
           dchain_allocated_fp(ch, idx));
    }
  }
  @*/

/*@
  fixpoint bool engaged_cell<kt>(pair<kt, bool> p) {
    return !snd(p);
  }
  @*/

/*@
  predicate map_vec_chain_coherent<kt>(list<pair<kt, int> > m,
                                       list<pair<kt, bool> > v, dchain ch) =
    dchain_index_range_fp(ch) == length(v) &*&
    true == forall_idx(v, 0, (consistent_pair)(m, ch)) &*&
    true == msubset(map(fst, m), map(fst, filter(engaged_cell, v))) &*&
    map_size_fp(m) == length(dchain_indexes_fp(ch));
  @*/

/*@
  lemma void mvc_coherent_bounds<kt>(list<pair<kt, int> > m,
                                     list<pair<kt, bool> > v, dchain ch)
  requires map_vec_chain_coherent<kt>(m, v, ch);
  ensures dchain_index_range_fp(ch) == length(v) &*&
          map_vec_chain_coherent<kt>(m, v, ch);
  {
    open map_vec_chain_coherent(m, v, ch);
    close map_vec_chain_coherent(m, v, ch);
  }
  @*/

/*@
  lemma void mvc_coherent_index_busy<kt>(list<pair<kt, int> > m,
                                         list<pair<kt, bool> > v, dchain ch,
                                         uint32_t index)
  requires map_vec_chain_coherent<kt>(m, v, ch) &*&
           true == dchain_allocated_fp(ch, index) &*&
           0 <= index &*& index < dchain_index_range_fp(ch);
  ensures map_vec_chain_coherent<kt>(m, v, ch) &*&
          nth(index, v) == pair(?key, false) &*&
          true == map_has_fp(m, key) &*&
          map_get_fp(m, key) == index;
  {
    mvc_coherent_bounds(m, v, ch);
    open map_vec_chain_coherent(m, v, ch);
    extract_prop_by_idx(v, (consistent_pair)(m, ch), 0, index);
    pair<kt, bool> p = nth(index, v);
    switch(p) {
      case pair(car, cdr):
    }
    close map_vec_chain_coherent(m, v, ch);
  }
  @*/

/*@
  lemma int pairs_consistent_get_index<kt>(list<pair<kt, int> > m,
                                           list<pair<kt, bool> > v, dchain ch,
                                           kt k, int start_idx)
  requires true == forall_idx(v, start_idx, (consistent_pair)(m, ch)) &*&
           true == map_has_fp(m, k) &*&
           true == mem(k, map(fst, filter(engaged_cell, v)));
  ensures 0 <= result - start_idx &*& result - start_idx < length(v) &*&
          true == consistent_pair(m, ch, result, nth(result - start_idx, v)) &*&
          result == map_get_fp(m, k) &*&
          true == dchain_allocated_fp(ch, result) &*&
          false == snd(nth(result - start_idx, v));
  {
    switch(v) {
      case nil:
        return 0;
      case cons(h, t):
        switch(h) { case pair(car, cdr):}
        if (h == pair(k, false)) {
          return start_idx;
        } else {
          return pairs_consistent_get_index(m, t, ch, k, start_idx + 1);
        }
    }
  }
  @*/

/*@
  lemma void mvc_coherent_map_get_bounded<kt>(list<pair<kt, int> > m,
                                              list<pair<kt, bool> > v, dchain ch,
                                              kt k)
  requires map_vec_chain_coherent<kt>(m, v, ch) &*&
           true == map_has_fp(m, k);
  ensures 0 <= map_get_fp(m, k) &*& map_get_fp(m, k) < length(v) &*&
          dchain_index_range_fp(ch) == length(v) &*&
          map_vec_chain_coherent<kt>(m, v, ch) &*&
          true == dchain_allocated_fp(ch, map_get_fp(m, k)) &*&
          false == snd(nth(map_get_fp(m, k), v));
  {
    mvc_coherent_bounds(m, v, ch);
    open map_vec_chain_coherent(m, v, ch);
    map_has_to_mem(m, k);
    msubset_subset(map(fst, m), map(fst, filter(engaged_cell, v)));
    subset_mem_trans(map(fst, m), map(fst, filter(engaged_cell, v)), k);
    pairs_consistent_get_index(m, v, ch, k, 0);
    close map_vec_chain_coherent(m, v, ch);
  }
  @*/

/*@
  lemma void mvc_coherent_map_get_vec_half<kt>(list<pair<kt, int> > m,
                                               list<pair<kt, bool> > v, dchain ch,
                                               kt k)
  requires map_vec_chain_coherent<kt>(m, v, ch) &*&
           true == map_has_fp(m, k);
  ensures 0 <= map_get_fp(m, k) &*& map_get_fp(m, k) < length(v) &*&
          dchain_index_range_fp(ch) == length(v) &*&
          map_vec_chain_coherent<kt>(m, v, ch) &*&
          true == dchain_allocated_fp(ch, map_get_fp(m, k)) &*&
          false == snd(nth(map_get_fp(m, k), v));
  {
    mvc_coherent_map_get_bounded(m, v, ch, k);
  }
  @*/

/*@
  lemma void rejuvenate_pairs_still_consistent<kt>(list<pair<kt, int> > m,
                                                   list<pair<kt, bool> > v, dchain ch,
                                                   int index, time_t time,
                                                   int start_idx)
  requires true == forall_idx(v, start_idx, (consistent_pair)(m, ch)) &*&
           true == dchain_allocated_fp(ch, index);
  ensures true == forall_idx(v, start_idx, (consistent_pair)(m, dchain_rejuvenate_fp(ch, index, time)));
  {
    switch(v) {
      case nil:
      case cons(h, t):
        switch(h) {
          case pair(car, cdr):
            dchain_rejuvenate_preserves_indexes_set(ch, index, time);
            dchain nch = dchain_rejuvenate_fp(ch, index, time);
            dchain_indexes_contain_index(ch, start_idx);
            dchain_indexes_contain_index(nch, start_idx);
            if (!cdr) {
              subset_mem_trans(dchain_indexes_fp(ch), dchain_indexes_fp(nch), start_idx);
            } else {
              if (dchain_allocated_fp(nch, start_idx))
                subset_mem_trans(dchain_indexes_fp(nch), dchain_indexes_fp(ch), start_idx);
            }
            rejuvenate_pairs_still_consistent(m, t, ch, index, time, start_idx + 1);
        }
    }
  }
  @*/

/*@
  lemma void mvc_rejuvenate_preserves_coherent<kt>(list<pair<kt, int> > m,
                                                   list<pair<kt, bool> > v, dchain ch,
                                                   int index, time_t time)
  requires map_vec_chain_coherent<kt>(m, v, ch) &*&
           true == dchain_allocated_fp(ch, index);
  ensures map_vec_chain_coherent<kt>(m, v, dchain_rejuvenate_fp(ch,
                                                                index,
                                                                time));
  {
    open map_vec_chain_coherent(m, v, ch);
    rejuvenate_pairs_still_consistent(m, v, ch, index, time, 0);
    rejuvenate_preserves_index_range(ch, index, time);
    dchain_rejuvenate_preserves_indexes_set(ch, index, time);
    close map_vec_chain_coherent(m, v, dchain_rejuvenate_fp(ch, index, time));
  }
  @*/

/*@
  lemma void mvc_coherent_alloc_is_halfowned<kt>(list<pair<kt, int> > m,
                                                 list<pair<kt, bool> > v, dchain ch,
                                                 int index)
  requires map_vec_chain_coherent<kt>(m, v, ch) &*&
           0 <= index &*& index < length(v);
  ensures map_vec_chain_coherent<kt>(m, v, ch) &*&
          snd(nth(index, v)) != dchain_allocated_fp(ch, index);
  {
    open map_vec_chain_coherent(m, v, ch);
    extract_prop_by_idx(v, (consistent_pair)(m, ch), 0, index);
    switch(nth(index, v)) {case pair(car, cdr):}
    close map_vec_chain_coherent(m, v, ch);
  }
  @*/

/*@
  lemma void consistent_pairs_no_key<kt>(list<pair<kt, int> > m,
                                         list<pair<kt, bool> > v, dchain ch,
                                         kt key,
                                         int start_idx)
  requires true == forall_idx(v, start_idx, (consistent_pair)(m, ch)) &*&
           false == map_has_fp(m, key);
  ensures false == mem(pair(key, false), v);
  {
    switch(v) {
      case nil:
      case cons(h, t):
        consistent_pairs_no_key(m, t, ch, key, start_idx + 1);
    }
  }
  @*/

/*@
  lemma void mvc_coherent_key_abscent<kt>(list<pair<kt, int> > m,
                                          list<pair<kt, bool> > v, dchain ch,
                                          kt key)
  requires map_vec_chain_coherent<kt>(m, v, ch) &*&
           false == map_has_fp(m, key);
  ensures map_vec_chain_coherent<kt>(m, v, ch) &*&
          false == mem(pair(key, false), v);
  {
    mvc_coherent_bounds(m, v, ch);
    open map_vec_chain_coherent(m, v, ch);
    consistent_pairs_no_key(m, v, ch, key, 0);
    close map_vec_chain_coherent(m, v, ch);
  }
  @*/

/*@
  lemma void mvc_coherent_same_len<kt>(list<pair<kt, int> > m,
                                       list<pair<kt, bool> > v, dchain ch)
  requires map_vec_chain_coherent<kt>(m, v, ch);
  ensures map_vec_chain_coherent<kt>(m, v, ch) &*&
          length(v) == dchain_index_range_fp(ch) &*&
          length(m) == length(dchain_indexes_fp(ch));
  {
    open map_vec_chain_coherent(m, v, ch);
    close map_vec_chain_coherent(m, v, ch);
  }
  @*/

/*@
  lemma void kkeeper_add_unrelevant<t>(list<void*> addrs,
                                       list<pair<t, bool> > contents,
                                       list<pair<t, void*> > addr_map,
                                       t v,
                                       void* addr)
  requires true == forall2(contents, addrs, (kkeeper)(addr_map)) &*&
           false == mem(pair(v, false), contents);
  ensures true == forall2(contents, addrs, (kkeeper)(map_put_fp(addr_map, v, addr)));
  {
    switch(contents) {
      case nil:
      case cons(cnt_h, cnt_t):
        switch(addrs) {
          case nil:
          case cons(addr_h, addr_t):
            switch(cnt_h) { case pair(car,cdr):}
            kkeeper_add_unrelevant(addr_t, cnt_t, addr_map, v, addr);
        }
    }
  }
  @*/

/*@
  lemma void kkeeper_add_one<t>(list<void*> addrs,
                                list<pair<t, bool> > contents,
                                list<pair<t, void*> > addr_map,
                                t v,
                                int index)
  requires 0 <= index &*& index < length(contents) &*&
           true == forall2(contents, addrs, (kkeeper)(addr_map)) &*&
           false == mem(pair(v, false), contents);
  ensures true == forall2(update(index, pair(v, false), contents),
                          addrs,
                          (kkeeper)(map_put_fp(addr_map, v,
                                               nth(index, addrs))));
  {
     switch(contents) {
       case nil:
       case cons(cnt_h, cnt_t):
         switch(addrs) {
           case nil:
           case cons(addr_h, addr_t):
             switch(cnt_h) { case pair(fff,sss):}
             if (index == 0) {
               kkeeper_add_unrelevant(addr_t, cnt_t, addr_map, v, nth(index, addrs));
             } else {
               kkeeper_add_one(addr_t, cnt_t, addr_map, v, index - 1);
             }
         }
     }
  }
  @*/

/*@
  lemma void empty_map_vec_dchain_consistent_pairs<kt>(list<pair<kt, bool> > vec, int len, int start_idx)
  requires true == forall(vec, snd);
  ensures true == forall_idx(vec, start_idx, (consistent_pair)(nil, empty_dchain_fp(len, 0)));
  {
    switch(vec) {
      case nil:
      case cons(h, t):
        switch(h) {case pair(car, cdr):}
        empty_map_vec_dchain_consistent_pairs(t, len, start_idx + 1);
    }
  }
  @*/

/*@
  lemma void empty_map_vec_dchain_coherent<kt>(list<pair<kt, bool> > vec)
  requires true == forall(vec, snd);
  ensures map_vec_chain_coherent<kt>(nil, vec,
                                     empty_dchain_fp(length(vec), 0));
  {
    empty_map_vec_dchain_consistent_pairs(vec, length(vec), 0);
    close map_vec_chain_coherent<kt>(nil, vec, empty_dchain_fp(length(vec), 0));
  }
  @*/

/*@
  lemma void remove_small_idx_still_consistent_pairs<kt>(list<pair<kt, int> > m,
                                                         list<pair<kt, bool> > v,
                                                         dchain ch,
                                                         int start_idx,
                                                         int shift)
  requires 0 < shift &*&
           true == forall_idx(v, start_idx + shift, (consistent_pair)(m, ch));
  ensures true == forall_idx(v, start_idx + shift, (consistent_pair)(m, dchain_remove_index_fp(ch, start_idx)));
  {
    switch(v) {
      case nil:
      case cons(h,t): switch(h) { case pair(key, present):
        remove_small_idx_still_consistent_pairs(m, t, ch, start_idx, shift + 1);
        dchain_remove_idx_from_indexes(ch, start_idx);
        dchain_indexes_contain_index(ch, start_idx + shift);
        dchain_indexes_contain_index(dchain_remove_index_fp(ch, start_idx), start_idx + shift);
        neq_mem_remove(start_idx + shift, start_idx, dchain_indexes_fp(ch));
      }
    }
  }

  @*/

/*@
  lemma void filter_engaged_len<kt>(list<pair<kt, int> > m,
                                    list<pair<kt, bool> > v,
                                    dchain ch, int start_idx)
  requires true == forall_idx(v, start_idx, (consistent_pair)(m, ch));
  ensures length(filter(engaged_cell, v)) <= length(dchain_indexes_fp(ch));
  {
    switch(v) {
      case nil:
      case cons(h, t):
        switch(h) { case pair(key,present):
          if (!present) {
            remove_small_idx_still_consistent_pairs(m, t, ch, start_idx, 1);
            dchain_remove_idx_from_indexes(ch, start_idx);
            dchain_indexes_contain_index(ch, start_idx);
            assert length(dchain_indexes_fp(dchain_remove_index_fp(ch, start_idx))) <
                   length(dchain_indexes_fp(ch));
            filter_engaged_len(m, t, dchain_remove_index_fp(ch, start_idx), start_idx + 1);
          } else {
            filter_engaged_len(m, t, ch, start_idx + 1);
          }
        }
    }
  }
  @*/

/*@
  lemma void mvc_coherent_dchain_map_same_size<kt>(list<pair<kt, int> > m,
                                                   list<pair<kt, bool> > v, dchain ch)
  requires map_vec_chain_coherent<kt>(m, v, ch);
  ensures map_vec_chain_coherent<kt>(m, v, ch) &*&
          map_size_fp(m) == length(dchain_indexes_fp(ch));
  {
    open map_vec_chain_coherent(m, v, ch);
    close map_vec_chain_coherent(m, v, ch);
  }
  @*/

/*@
  lemma void mvc_coherent_dchain_non_out_of_space_map_nonfull<kt>(list<pair<kt, int> > m,
                                                                  list<pair<kt, bool> > v, dchain ch)
  requires map_vec_chain_coherent<kt>(m, v, ch) &*&
           dchain_out_of_space_fp(ch) == false;
  ensures map_vec_chain_coherent<kt>(m, v, ch) &*&
          map_size_fp(m) < dchain_index_range_fp(ch);
  {
    open map_vec_chain_coherent(m, v, ch);
    msubset_length(map(fst, m), map(fst, filter(engaged_cell, v)));
    map_preserves_length(fst, m);
    assert length(m) == length(map(fst, m));
    assert length(m) <= length(map(fst, filter(engaged_cell, v)));
    map_preserves_length(fst, filter(engaged_cell, v));
    assert length(map(fst, filter(engaged_cell, v))) <= length(filter(engaged_cell, v));
    filter_engaged_len(m, v, ch, 0);
    dchain_out_of_space_to_indexes_size(ch);
    assert length(filter(engaged_cell, v)) < length(v);
    close map_vec_chain_coherent(m, v, ch);
  }
  @*/

/*@
  lemma void add_unrelevant_entry_consistent_pairs<kt>(list<pair<kt, int> > m,
                                                       list<pair<kt, bool> > v, dchain ch,
                                                       int index, time_t time,
                                                       kt key,
                                                       int start_idx)
  requires index < start_idx &*&
           true == forall_idx(v, start_idx, (consistent_pair)(m, ch)) &*&
           false == mem(key, map(fst, m));
  ensures true == forall_idx(v,
                             start_idx,
                             (consistent_pair)(map_put_fp(m, key, index),
                                               dchain_allocate_fp(ch, index, time)));
  {
    switch(v) {
      case nil:
      case cons(h,t): switch(h) { case pair(cur_key, present):
        dchain_allocate_append_to_indexes(ch, index, time);
        dchain_indexes_contain_index(ch, start_idx);
        dchain_indexes_contain_index(dchain_allocate_fp(ch, index, time), start_idx);
        map_has_to_mem(m, key);
        add_unrelevant_entry_consistent_pairs(m, t, ch, index, time, key, start_idx + 1);
      }
    }
  }

  lemma void add_entry_consistent_pairs<kt>(list<pair<kt, int> > m,
                                            list<pair<kt, bool> > v, dchain ch,
                                            int index, time_t time,
                                            kt key,
                                            int start_idx)
  requires true == forall_idx(v, start_idx, (consistent_pair)(m, ch)) &*&
           false == mem(key, map(fst, m));
  ensures true == forall_idx(update(index - start_idx, pair(key, false), v),
                             start_idx,
                             (consistent_pair)(map_put_fp(m, key, index),
                                               dchain_allocate_fp(ch, index, time)));
  {
    switch(v) {
      case nil:
      case cons(h,t): switch(h) { case pair(cur_key, present):
        dchain_allocate_append_to_indexes(ch, index, time);
        dchain_indexes_contain_index(ch, start_idx);
        dchain_indexes_contain_index(dchain_allocate_fp(ch, index, time), start_idx);
        if (index == start_idx) {
          add_unrelevant_entry_consistent_pairs(m, t, ch, index, time, key, start_idx + 1);
        } else {
          map_has_to_mem(m, key);
          add_entry_consistent_pairs(m, t, ch, index, time, key, start_idx + 1);
        }
      }
    }
  }

  lemma void remove_key_from_vec<kt>(list<pair<kt, bool> > v, kt key)
  requires true;
  ensures remove(key, map(fst, filter(engaged_cell, v))) ==
          map(fst, filter(engaged_cell, remove(pair(key, false), v)));
  {
    switch(v) {
      case nil:
      case cons(h,t): switch(h) { case pair(k,eng):
        if (h != pair(key, false)) remove_key_from_vec(t, key);
      }
    }
  }
@*/

/*@
  lemma void update_remove_same_msubset<t>(int i, t el, list<t> l)
  requires 0 <= i &*& true == mem(el, l);
  ensures (index_of(el, l) <= i) ?
             true == msubset(update(i, el, remove(el, l)),
                             remove(el, update(i + 1, el, l))) :
             true == msubset(update(i, el, remove(el, l)),
                             remove(el, update(i, el, l)));
  {
    switch(l) {
      case nil:
      case cons(h,t):
        if (i == 0) {
          if (h == el) {
            assert update(i, el, remove(el, l)) == update(0, el, t);
            assert remove(el, update(i + 1, el, l)) == update(0, el, t);
            msubset_refl(update(i, el, remove(el, l)));
          } else {
            assert remove(el, update(i, el, l)) == t;
            assert update(i, el, remove(el, l)) == cons(el, remove(el, t));
            pull_to_start_msubset2(t, el);
            index_of_positive(el, t);
          }
        } else {
          if (h == el) {
            msubset_refl(update(i, el, t));
          } else {
            update_remove_same_msubset(i - 1, el, t);
          }
        }
    }
  }

  lemma void update_remove_msubset<t>(int i, t el1, t el2, list<t> l)
  requires 0 <= i &*& true == mem(el2, l);
  ensures (index_of(el2, l) <= i) ?
             true == msubset(update(i, el1, remove(el2, l)),
                             remove(el2, update(i + 1, el1, l))) :
             true == msubset(update(i, el1, remove(el2, l)),
                             remove(el2, update(i, el1, l)));
  {
    if (el1 != el2) {
      update_remove(i, el1, el2, l);
      msubset_refl(update(i, el1, remove(el2, l)));
      return;
    } else {
      update_remove_same_msubset(i, el1, l);
    }
  }
@*/
/*@

  lemma void particular_map_remove<t>(t key, list<pair<t, bool> > l)
  requires true == forall(l, engaged_cell);
  ensures map(fst, remove(pair(key, false), l)) == remove(key, map(fst, l));
  {
    switch(l) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(f,s): }
        if (h != pair(key, false))
          particular_map_remove(key, t);
    }
  }

  lemma void particular_mem_map_filter<t>(t el, list<pair<t, bool> > l)
  requires true == mem(el, map(fst, filter(engaged_cell, l)));
  ensures true == mem(pair(el, false), filter(engaged_cell, l));
  {
    switch(l) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(lhs,rhs): }
        if (pair(el, false) != h)
          particular_mem_map_filter(el, t);
    }
  }


  lemma void msubset_remove_map_filter<t1,t2>(list<t2> l1,
                                              t1 el,
                                              fixpoint(t1,t2) f1,
                                              fixpoint(t1,bool) f2,
                                              list<t1> l2)
  requires true == f2(el) &*& true == msubset(l1, remove(f1(el), map(f1, filter(f2, l2))));
  ensures  true == msubset(l1, map(f1, filter(f2, remove(el, l2))));
  {
    assume(false);//TODO
  }

  lemma void add_entry_preserves_msubset_tail<kt>(list<pair<kt, int> > m,
                                                  list<pair<kt, bool> > v,
                                                  int index,
                                                  kt key)
  requires true == msubset(map(fst, m), map(fst, filter(engaged_cell, v))) &*&
           0 <= index &*& index < length(v) &*&
           true == snd(nth(index, v));
  ensures true == msubset(map(fst, m),
                          map(fst, filter(engaged_cell, update(index, pair(key, false), v))));
  {
    switch(m) {
      case nil:
      case cons(h,t): switch(h) { case pair(cur_key, cur_val):
        assert true == msubset(map(fst, t), remove(cur_key, map(fst, filter(engaged_cell, v))));
        msubset_remove_map_filter(map(fst, t), pair(cur_key, false), fst, engaged_cell, v);
        assert true == mem(cur_key, map(fst, filter(engaged_cell, v)));
        particular_mem_map_filter(cur_key, v);
        assert true == mem(pair(cur_key, false), filter(engaged_cell, v));
        mem_unfilter(pair(cur_key, false), engaged_cell, v);
        assert true == mem(pair(cur_key, false), v);
        if (index_of(pair(cur_key, false), v) == index) {
          mem_nth_index_of(pair(cur_key, false), v);
          assert nth(index_of(pair(cur_key, false), v), v) == pair(cur_key, false);
          assert nth(index, v) == pair(cur_key, false);
          assert true == snd(nth(index, v));
          assert false;
        }
        assert index_of(pair(cur_key, false), v) != index;
        mem_update_unrelevant(pair(cur_key, false), index, pair(key, false), v);
        assert true == mem(pair(cur_key, false), update(index, pair(key, false), v));
        filter_mem(pair(cur_key, false), update(index, pair(key, false), v), engaged_cell);
        assert true == mem(pair(cur_key, false), filter(engaged_cell, update(index, pair(key, false), v)));
        mem_map(pair(cur_key, false), filter(engaged_cell, update(index, pair(key, false), v)), fst);
        assert true == mem(cur_key, map(fst, filter(engaged_cell, update(index, pair(key, false), v))));
        assert true == mem(pair(cur_key, false), v);
        nth_remove(index, pair(cur_key, false), v);
        if (index_of(pair(cur_key, false), v) < index) {
          assert nth(index, v) == nth(index - 1, remove(pair(cur_key, false), v));
          add_entry_preserves_msubset_tail(t, remove(pair(cur_key, false), v), index - 1, key);
          assert true == msubset(map(fst, t), map(fst, filter(engaged_cell, update(index - 1, pair(key, false), remove(pair(cur_key, false), v)))));
          update_remove_msubset(index - 1, pair(key, false), pair(cur_key, false), v);
          msubset_filter(engaged_cell, update(index - 1, pair(key, false), remove(pair(cur_key, false), v)),remove(pair(cur_key, false), update(index, pair(key, false), v)));
          msubset_map(fst,
                      filter(engaged_cell, update(index - 1, pair(key, false), remove(pair(cur_key, false), v))),
                      filter(engaged_cell, remove(pair(cur_key, false), update(index, pair(key, false), v))));
          msubset_trans(map(fst, t),
                        map(fst, filter(engaged_cell, update(index - 1, pair(key, false), remove(pair(cur_key, false), v)))),
                        map(fst, filter(engaged_cell, remove(pair(cur_key, false), update(index, pair(key, false), v)))));
        } else {
          assert length(v) - 1 <= length(remove(pair(cur_key, false), v));
          assert index < index_of(pair(cur_key, false), v);
          mem_index_of(pair(cur_key, false), v);
          assert index_of(pair(cur_key, false), v) < length(v);
          add_entry_preserves_msubset_tail(t, remove(pair(cur_key, false), v), index, key);
          assert true == msubset(map(fst, t), map(fst, filter(engaged_cell, update(index, pair(key, false), remove(pair(cur_key, false), v)))));
          update_remove_msubset(index, pair(key, false), pair(cur_key, false), v);
          msubset_filter(engaged_cell,
                         update(index, pair(key, false), remove(pair(cur_key, false), v)),
                         remove(pair(cur_key, false), update(index, pair(key, false), v)));
          msubset_map(fst,
                      filter(engaged_cell, update(index, pair(key, false), remove(pair(cur_key, false), v))),
                      filter(engaged_cell, remove(pair(cur_key, false), update(index, pair(key, false), v))));
          msubset_trans(map(fst, t),
                        map(fst, filter(engaged_cell, update(index, pair(key, false), remove(pair(cur_key, false), v)))),
                        map(fst, filter(engaged_cell, remove(pair(cur_key, false), update(index, pair(key, false), v)))));
        }

        assert true == msubset(map(fst, t), map(fst, filter(engaged_cell, remove(pair(cur_key, false), update(index, pair(key, false), v)))));
        filter_remove(engaged_cell, pair(cur_key, false), update(index, pair(key, false), v));
        assert true == msubset(map(fst, t), map(fst, remove(pair(cur_key, false), filter(engaged_cell, update(index, pair(key, false), v)))));
        filter_forall(engaged_cell, update(index, pair(key, false), v));
        particular_map_remove(cur_key, filter(engaged_cell, update(index, pair(key, false), v)));
        assert true == msubset(map(fst, t), remove(cur_key, map(fst, filter(engaged_cell, update(index, pair(key, false), v)))));
      }
    }
  }

  lemma void add_entry_preserves_msubset<kt>(list<pair<kt, int> > m,
                                             list<pair<kt, bool> > v,
                                             int index,
                                             kt key)
  requires true == msubset(map(fst, m), map(fst, filter(engaged_cell, v))) &*&
           0 <= index &*& index < length(v) &*&
           false == mem(key, map(fst, m)) &*&
           true == snd(nth(index, v));
  ensures true == msubset(map(fst, map_put_fp(m, key, index)),
                          map(fst, filter(engaged_cell, update(index, pair(key, false), v))));
  {
    add_entry_preserves_msubset_tail(m, v, index, key);
    mem_update(pair(key, false), index, v);
    filter_mem(pair(key, false), update(index, pair(key, false), v), engaged_cell);
    mem_map(pair(key, false), filter(engaged_cell, update(index, pair(key, false), v)), fst);
    msubset_remove(map(fst, m), map(fst, filter(engaged_cell, update(index, pair(key, false), v))), key);
    remove_nonmem(key, map(fst,m));
  }

  lemma void mvc_coherent_put<kt>(list<pair<kt, int> > m,
                                  list<pair<kt, bool> > v, dchain ch,
                                  int index, time_t time,
                                  kt key)
  requires map_vec_chain_coherent<kt>(m, v, ch) &*&
           false == dchain_allocated_fp(ch, index) &*&
           false == map_has_fp(m, key) &*&
           true == snd(nth(index, v)) &*&
           0 <= index &*& index < length(v);
  ensures map_vec_chain_coherent<kt>(map_put_fp(m, key, index),
                                     update(index, pair(key, false), v),
                                     dchain_allocate_fp(ch, index, time));
  {
    open map_vec_chain_coherent(m, v, ch);

    assert dchain_index_range_fp(ch) == length(v) &*&
           true == forall_idx(v, 0, (consistent_pair)(m, ch)) &*&
           true == msubset(map(fst, m), map(fst, filter(engaged_cell, v))) &*&
           map_size_fp(m) == length(dchain_indexes_fp(ch));

    allocate_preserves_index_range(ch, index, time);
    dchain_allocate_append_to_indexes(ch, index, time);
    assert dchain_index_range_fp(dchain_allocate_fp(ch, index, time)) == length(update(index, pair(key, false), v));
    assert map_size_fp(map_put_fp(m, key, index)) == length(dchain_indexes_fp(dchain_allocate_fp(ch, index, time)));

    map_has_to_mem(m, key);
    assert false == mem(key, map(fst, m));
    add_entry_consistent_pairs(m, v, ch, index, time, key, 0);
    assert true == forall_idx(update(index, pair(key, false), v), 0,
                              (consistent_pair)(map_put_fp(m, key, index), dchain_allocate_fp(ch, index, time)));

    add_entry_preserves_msubset(m, v, index, key);
    assert true == msubset(map(fst, map_put_fp(m, key, index)),
                           map(fst, filter(engaged_cell, update(index, pair(key, false), v))));

    close map_vec_chain_coherent(map_put_fp(m, key, index),
                                 update(index, pair(key, false), v),
                                 dchain_allocate_fp(ch, index, time));
  }
  @*/

/*@
  lemma void mvc_coherent_expire_one<kt>(list<pair<kt, int> > m,
                                         list<pair<kt, bool> > v, dchain ch,
                                         int index,
                                         kt key)
  requires map_vec_chain_coherent<kt>(m, v, ch) &*&
           nth(index, v) == pair(key, false);
  ensures map_vec_chain_coherent<kt>(map_erase_fp(m, key),
                                     vector_erase_fp(v, index),
                                     dchain_remove_index_fp(ch, index));
  {
    assume(false);//TODO
  }
  @*/
