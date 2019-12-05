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
              int index, vigor_time_t time)
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
 vt value, int ind, vigor_time_t t,
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
                                           list<pair<t, real> > contents,
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

  fixpoint bool owned_or_not_this<t>(t val, pair<t, real> cell) {
    return snd(cell) == 1.0 || fst(cell) != val;
  }

  lemma void kkeeper_erase_one_from_map<t>(list<void*> addrs,
                                           list<pair<t, real> > contents,
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
            if (snd(ch) != 1.0) {
              map_erase_keeps_others(addr_map, val, fst(ch));
            }
            kkeeper_erase_one_from_map(at, ct, addr_map, val);
      }
    }
  }

  lemma void kkeeper_nth_addrs_is_map_get<t>(list<void*> addrs,
                                             list<pair<t, real> > contents,
                                             list<pair<t, void*> > addr_map,
                                             int index)
  requires 0 <= index &*& index < length(contents) &*&
           length(contents) <= length(addrs) &*&
           true == forall2(contents, addrs, (kkeeper)(addr_map)) &*&
           nth(index, contents) == pair(?val, ?frac) &*&
           frac != 1.0;
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
                                        list<pair<t, real> > contents,
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
                                                  list<pair<t, real> > contents,
                                                  list<pair<t, void*> > addr_map,
                                                  int index)
  requires 0 <= index &*& index < length(contents) &*&
           length(contents) <= length(addrs) &*&
           true == forall2(contents, addrs, (kkeeper)(addr_map)) &*&
           nth(index, contents) == pair(?val, ?frac) &*&
           frac != 1.0 &*&
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
            if (snd(ch) != 1.0) {
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
                                  list<pair<t, real> > contents,
                                  list<pair<t, void*> > addr_map,
                                  int index)
  requires 0 <= index &*& index < length(contents) &*&
           length(contents) <= length(addrs) &*&
           true == forall2(contents, addrs, (kkeeper)(addr_map)) &*&
           nth(index, contents) == pair(?val, ?frac) &*&
           frac != 1.0 &*&
           true == no_dups(addrs);
  ensures true == forall2(vector_erase_fp(contents, index), addrs,
                          (kkeeper)(map_erase_fp(addr_map, val)));
  {
    kkeeper_erase_one_from_vec(addrs, contents, addr_map, index);
    nth_update(index, index, pair(val, 1.0), contents);
    kkeeper_no_dups_owned_or_not_this(addrs, contents, addr_map, index);
    kkeeper_erase_one_from_map(addrs, vector_erase_fp(contents, index),
                               addr_map, val);
  }
  @*/

/*@
  lemma void empty_kkeeper<t>(list<void*> addrs,
                              list<pair<t, real> > contents,
                              list<pair<t, void*> > addr_map,
                              int capacity)
  requires length(contents) == capacity &*&
           true == forall(contents, is_one);
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
                                    int idx, pair<kt, real> el) {
    switch(el) {
      case pair(car, cdr):
        return cdr == 1.0 ?
          (false == dchain_allocated_fp(ch, idx))
          :
          (cdr == 0.75 &&
           map_has_fp(m, car) &&
           map_get_fp(m, car) == idx &&
           dchain_allocated_fp(ch, idx));
    }
  }
  @*/

/*@
  predicate map_vec_chain_coherent<kt>(list<pair<kt, int> > m,
                                       list<pair<kt, real> > v,
                                       dchain ch) =
    dchain_index_range_fp(ch) == length(v) &*&
    true == forall_idx(v, 0, (consistent_pair)(m, ch)) &*&
    true == msubset(map(fst, m), map(fst, filter(engaged_cell, v))) &*&
    map_size_fp(m) == length(dchain_indexes_fp(ch));
  @*/

/*@
  lemma void mvc_coherent_bounds<kt>(list<pair<kt, int> > m,
                                     list<pair<kt, real> > v,
                                     dchain ch)
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
                                         list<pair<kt, real> > v,
                                         dchain ch,
                                         uint32_t index)
  requires map_vec_chain_coherent<kt>(m, v, ch) &*&
           true == dchain_allocated_fp(ch, index) &*&
           0 <= index &*& index < dchain_index_range_fp(ch);
  ensures map_vec_chain_coherent<kt>(m, v, ch) &*&
          nth(index, v) == pair(?key, ?frac) &*&
          frac == 0.75 &*&
          true == map_has_fp(m, key) &*&
          map_get_fp(m, key) == index;
  {
    mvc_coherent_bounds(m, v, ch);
    open map_vec_chain_coherent(m, v, ch);
    extract_prop_by_idx(v, (consistent_pair)(m, ch), 0, index);
    pair<kt, real> p = nth(index, v);
    switch(p) {
      case pair(car, cdr):
        assert true == map_has_fp(m, car);
        assert map_get_fp(m, car) == index;
        assert true == dchain_allocated_fp(ch, index);
        assert cdr == 0.75;
    }
    close map_vec_chain_coherent(m, v, ch);
  }
  @*/

/*@
  lemma int pairs_consistent_get_index<kt>(list<pair<kt, int> > m,
                                           list<pair<kt, real> > v,
                                           dchain ch,
                                           kt k, int start_idx)
  requires true == forall_idx(v, start_idx, (consistent_pair)(m, ch)) &*&
           true == map_has_fp(m, k) &*&
           true == mem(k, map(fst, filter(engaged_cell, v)));
  ensures 0 <= result - start_idx &*& result - start_idx < length(v) &*&
          true == consistent_pair(m, ch, result, nth(result - start_idx, v)) &*&
          true == dchain_allocated_fp(ch, result) &*&
          result == map_get_fp(m, k) &*&
          1.0 != snd(nth(result - start_idx, v));
  {
    switch(v) {
      case nil:
        return 0;
      case cons(h, t):
        switch(h) { case pair(car, cdr):
            if (car == k && cdr != 1.0) {
              return start_idx;
            } else {
              return pairs_consistent_get_index(m, t, ch, k, start_idx + 1);
            }
        }
    }
  }
  @*/

/*@
  lemma void mvc_coherent_map_get_bounded<kt>(list<pair<kt, int> > m,
                                              list<pair<kt, real> > v,
                                              dchain ch,
                                              kt k)
  requires map_vec_chain_coherent<kt>(m, v, ch) &*&
           true == map_has_fp(m, k);
  ensures 0 <= map_get_fp(m, k) &*& map_get_fp(m, k) < length(v) &*&
          dchain_index_range_fp(ch) == length(v) &*&
          map_vec_chain_coherent<kt>(m, v, ch) &*&
          true == dchain_allocated_fp(ch, map_get_fp(m, k)) &*&
          1.0 != snd(nth(map_get_fp(m, k), v));
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
                                               list<pair<kt, real> > v,
                                               dchain ch,
                                               kt k)
  requires map_vec_chain_coherent<kt>(m, v, ch) &*&
           true == map_has_fp(m, k);
  ensures 0 <= map_get_fp(m, k) &*& map_get_fp(m, k) < length(v) &*&
          dchain_index_range_fp(ch) == length(v) &*&
          map_vec_chain_coherent<kt>(m, v, ch) &*&
          true == dchain_allocated_fp(ch, map_get_fp(m, k)) &*&
          1.0 != snd(nth(map_get_fp(m, k), v));
  {
    mvc_coherent_map_get_bounded(m, v, ch, k);
  }
  @*/

/*@
  lemma void rejuvenate_pairs_still_consistent<kt>(list<pair<kt, int> > m,
                                                   list<pair<kt, real> > v,
                                                   dchain ch,
                                                   int index, vigor_time_t time,
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
            if (cdr != 1.0) {
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
                                                   list<pair<kt, real> > v,
                                                   dchain ch,
                                                   int index, vigor_time_t time)
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
                                                 list<pair<kt, real> > v,
                                                 dchain ch,
                                                 int index)
  requires map_vec_chain_coherent<kt>(m, v, ch) &*&
           0 <= index &*& index < length(v);
  ensures map_vec_chain_coherent<kt>(m, v, ch) &*&
          (snd(nth(index, v)) == 1.0) != dchain_allocated_fp(ch, index);
  {
    open map_vec_chain_coherent(m, v, ch);
    extract_prop_by_idx(v, (consistent_pair)(m, ch), 0, index);
    switch(nth(index, v)) {case pair(car, cdr):}
    close map_vec_chain_coherent(m, v, ch);
  }
  @*/

/*@
  lemma void consistent_pairs_no_key<kt>(list<pair<kt, int> > m,
                                         list<pair<kt, real> > v,
                                         dchain ch,
                                         kt key,
                                         int start_idx)
  requires true == forall_idx(v, start_idx, (consistent_pair)(m, ch)) &*&
           false == map_has_fp(m, key);
  ensures true == forall(v, (is_one_if_equals)(key));
  {
    switch(v) {
      case nil:
      case cons(h, t):
        if (fst(h) == key) {
          assert true == consistent_pair(m, ch, start_idx, h);
          // Yes, VeriFast actually requires inlining the very thing we just asserted :(
          switch(h) { case pair(car, cdr):
            assert cdr == 1.0 ? (false == dchain_allocated_fp(ch, start_idx))
                              : (cdr == 0.75 && map_has_fp(m, car) &&
                                 map_get_fp(m, car) == start_idx && dchain_allocated_fp(ch, start_idx));
          }
          assert false == map_has_fp(m, fst(h));
          assert snd(h) == 1.0;
          assert true == is_one_if_equals(key, h);
        }
        consistent_pairs_no_key(m, t, ch, key, start_idx + 1);
    }
  }
  @*/

/*@
  lemma void mvc_coherent_key_abscent<kt>(list<pair<kt, int> > m,
                                          list<pair<kt, real> > v,
                                          dchain ch,
                                          kt key)
  requires map_vec_chain_coherent<kt>(m, v, ch) &*&
           false == map_has_fp(m, key);
  ensures map_vec_chain_coherent<kt>(m, v, ch) &*&
          true == forall(v, (is_one_if_equals)(key));
  {
    mvc_coherent_bounds(m, v, ch);
    open map_vec_chain_coherent(m, v, ch);
    consistent_pairs_no_key(m, v, ch, key, 0);
    close map_vec_chain_coherent(m, v, ch);
  }
  @*/

/*@
  lemma void mvc_coherent_same_len<kt>(list<pair<kt, int> > m,
                                       list<pair<kt, real> > v,
                                       dchain ch)
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
                                       list<pair<t, real> > contents,
                                       list<pair<t, void*> > addr_map,
                                       t v,
                                       void* addr)
  requires true == forall2(contents, addrs, (kkeeper)(addr_map)) &*&
           true == forall(contents, (is_one_if_equals)(v));
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
                                list<pair<t, real> > contents,
                                list<pair<t, void*> > addr_map,
                                t v,
                                int index)
  requires 0 <= index &*& index < length(contents) &*&
           true == forall2(contents, addrs, (kkeeper)(addr_map)) &*&
           true == forall(contents, (is_one_if_equals)(v));
  ensures true == forall2(update(index, pair(v, 0.75), contents),
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
  lemma void empty_map_vec_dchain_consistent_pairs<kt>(list<pair<kt, real> > vec, int len, int start_idx)
  requires true == forall(vec, is_one);
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
  lemma void empty_map_vec_dchain_coherent<kt>(list<pair<kt, real> > vec)
  requires true == forall(vec, is_one);
  ensures map_vec_chain_coherent<kt>(nil, vec,
                                     empty_dchain_fp(length(vec), 0));
  {
    empty_map_vec_dchain_consistent_pairs(vec, length(vec), 0);
    close map_vec_chain_coherent<kt>(nil, vec, empty_dchain_fp(length(vec), 0));
  }
  @*/

/*@
  lemma void remove_small_idx_still_consistent_pairs<kt>(list<pair<kt, int> > m,
                                                         list<pair<kt, real> > v,
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
                                    list<pair<kt, real> > v,
                                    dchain ch, int start_idx)
  requires true == forall_idx(v, start_idx, (consistent_pair)(m, ch));
  ensures length(filter(engaged_cell, v)) <= length(dchain_indexes_fp(ch));
  {
    switch(v) {
      case nil:
      case cons(h, t):
        switch(h) { case pair(key,present):
          if (present != 1.0) {
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
                                                   list<pair<kt, real> > v, dchain ch)
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
                                                                  list<pair<kt, real> > v,
                                                                  dchain ch)
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
                                                       list<pair<kt, real> > v, dchain ch,
                                                       int index, vigor_time_t time,
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
                                            list<pair<kt, real> > v, dchain ch,
                                            int index, vigor_time_t time,
                                            kt key,
                                            int start_idx)
  requires true == forall_idx(v, start_idx, (consistent_pair)(m, ch)) &*&
           false == mem(key, map(fst, m));
  ensures true == forall_idx(update(index - start_idx, pair(key, 0.75), v),
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
  lemma void particular_mem_map_filter<t>(t el, list<pair<t, real> > l)
  requires true == mem(el, map(fst, filter(engaged_cell, l)));
  ensures true == mem(el, map(fst, filter(engaged_cell, l))) &*&
          true == mem(el, map(fst, l));
  {
    switch(l) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(lhs,rhs): }
        if (!engaged_cell(h) ||
            fst(h) != el) {
          particular_mem_map_filter(el, t);
        }
    }
  }

  lemma void msubset_remove_map_filter<t1,t2>(list<t2> l1,
                                              t1 el,
                                              fixpoint(t1,t2) f1,
                                              fixpoint(t1,bool) f2,
                                              list<t1> l2)
  requires true == f2(el) &*&
           true == mem(el, l2) &*&
           true == msubset(l1, remove(f1(el), map(f1, filter(f2, l2))));
  ensures  true == msubset(l1, map(f1, filter(f2, remove(el, l2))));
  {
    filter_remove(f2, el, l2);
    filter_mem(el, l2, f2);
    multiset_eq_map_remove_swap(f1, el, filter(f2, l2));
    multiset_eq_msubset(map(f1, filter(f2, remove(el, l2))),
                        remove(f1(el), map(f1, filter(f2, l2))));
    msubset_trans(l1, remove(f1(el), map(f1, filter(f2, l2))),
                  map(f1, filter(f2, remove(el, l2))));
  }
@*/
/*@
  lemma void add_entry_preserves_msubset_tail<kt>(list<pair<kt, int> > m,
                                                  list<pair<kt, real> > v,
                                                  int index,
                                                  kt key,
                                                  real new_ownf)
  requires true == msubset(map(fst, m), map(fst, filter(engaged_cell, v))) &*&
           0 <= index &*& index < length(v) &*&
           1.0 == snd(nth(index, v)) &*&
           0.0 < new_ownf &*& new_ownf < 1.0;
  ensures true == msubset(map(fst, m),
                          map(fst, filter(engaged_cell,
                                          update(index, pair(key, new_ownf), v))));
  {
    switch(m) {
      case nil:
      case cons(h,t): switch(h) { case pair(cur_key, cur_val):
        particular_mem_map_filter(cur_key, v);
        assert true == mem(cur_key, map(fst, filter(engaged_cell, v)));
        real ownf = snd(nth(index_of(cur_key,
                                     map(fst, filter(engaged_cell, v))),
                            filter(engaged_cell, v)));

        map_preserves_length(fst, filter(engaged_cell, v));
        assert 0 <= index_of(cur_key, map(fst, filter(engaged_cell, v)));
        pair<kt, real> ppp = nth(index_of(cur_key,
                                          map(fst, filter(engaged_cell, v))),
                                 filter(engaged_cell, v));
        switch(ppp) { case pair(car,cdr):
          mem_nth_index_of(cur_key,
                           map(fst, filter(engaged_cell, v)));
          nth_map(index_of(cur_key,
                           map(fst, filter(engaged_cell, v))),
                  fst,
                  filter(engaged_cell, v));
          assert cur_key == fst(nth(index_of(cur_key,
                                             map(fst, filter(engaged_cell, v))),
                                    filter(engaged_cell, v)));
          assert car == cur_key;
          assert cdr == ownf;
        }
        assert true == mem(pair(cur_key, ownf), filter(engaged_cell, v));
        mem_unfilter(pair(cur_key, ownf), engaged_cell, v);
        assert ppp == pair(cur_key, ownf);
        assert true == mem(ppp, v);
        filter_forall(engaged_cell, v);
        forall_nth(filter(engaged_cell, v),
                   engaged_cell,
                   index_of(cur_key, map(fst, filter(engaged_cell, v))));
        if (index_of(pair(cur_key, ownf), v) == index) {
          mem_nth_index_of(pair(cur_key, ownf), v);
          assert nth(index_of(pair(cur_key, ownf), v), v) == ppp;
          assert false;
        }
        mem_update_unrelevant(pair(cur_key, ownf),
                              index,
                              pair(key, new_ownf),
                              v);
        filter_mem(pair(cur_key, ownf),
                   update(index, pair(key, new_ownf), v), engaged_cell);
        mem_map(pair(cur_key, ownf),
                filter(engaged_cell,
                       update(index, pair(key, new_ownf), v)),
                fst);
        msubset_remove_map_filter(map(fst, t),
                                  pair(cur_key, ownf),
                                  fst,
                                  engaged_cell,
                                  v);
        nth_remove(index, pair(cur_key, ownf), v);
        if (index_of(pair(cur_key, ownf), v) < index) {
          add_entry_preserves_msubset_tail(t,
                                           remove(pair(cur_key, ownf), v),
                                           index - 1,
                                           key,
                                           new_ownf);
          update_remove_msubset(index - 1,
                                pair(key, new_ownf),
                                pair(cur_key, ownf),
                                v);
          msubset_filter(engaged_cell,
                         update(index - 1,
                                pair(key, new_ownf),
                                remove(pair(cur_key, ownf), v)),
                         remove(pair(cur_key, ownf),
                                update(index, pair(key, new_ownf), v)));
          msubset_map(fst,
                      filter(engaged_cell,
                             update(index - 1, pair(key, new_ownf),
                                    remove(pair(cur_key, ownf), v))),
                      filter(engaged_cell,
                             remove(pair(cur_key, ownf),
                                    update(index, pair(key, new_ownf), v))));
          msubset_trans(map(fst, t),
                        map(fst, filter(engaged_cell,
                                        update(index - 1,
                                               pair(key, new_ownf),
                                               remove(pair(cur_key, ownf),
                                                      v)))),
                        map(fst, filter(engaged_cell,
                                        remove(pair(cur_key, ownf),
                                               update(index,
                                                      pair(key, new_ownf),
                                                      v)))));
        } else {
          mem_index_of(pair(cur_key, ownf), v);
          add_entry_preserves_msubset_tail
            (t, remove(pair(cur_key, ownf), v), index, key, new_ownf);
          update_remove_msubset
            (index, pair(key, new_ownf), pair(cur_key, ownf), v);
          msubset_filter(engaged_cell,
                         update(index,
                                pair(key, new_ownf),
                                remove(pair(cur_key, ownf), v)),
                         remove(pair(cur_key, ownf),
                                update(index, pair(key, new_ownf), v)));
          msubset_map(fst,
                      filter(engaged_cell,
                             update(index,
                                    pair(key, new_ownf),
                                    remove(pair(cur_key, ownf), v))),
                      filter(engaged_cell,
                             remove(pair(cur_key, ownf),
                                    update(index, pair(key, new_ownf), v))));
          msubset_trans(map(fst, t),
                        map(fst, filter(engaged_cell,
                                        update(index,
                                               pair(key, new_ownf),
                                               remove(pair(cur_key, ownf),
                                                      v)))),
                        map(fst, filter(engaged_cell,
                                        remove(pair(cur_key, ownf),
                                               update(index,
                                                      pair(key, new_ownf),
                                                      v)))));
        }

        filter_remove(engaged_cell,
                      pair(cur_key, ownf),
                      update(index, pair(key, new_ownf), v));
        filter_forall(engaged_cell,
                      update(index, pair(key, new_ownf), v));
        multiset_eq_map_remove_swap(fst,
                                    pair(cur_key, ownf),
                                    filter(engaged_cell,
                                           update(index,
                                                  pair(key, new_ownf),
                                                  v)));
        multiset_eq_msubset(map(fst, remove(pair(cur_key, ownf),
                                            filter(engaged_cell,
                                                   update(index,
                                                          pair(key, new_ownf),
                                                          v)))),
                            remove(cur_key,
                                   map(fst, filter(engaged_cell,
                                                   update(index,
                                                          pair(key, new_ownf),
                                                          v)))));
        msubset_trans(map(fst, t),
                      map(fst, remove(pair(cur_key, ownf),
                                      filter(engaged_cell,
                                             update(index,
                                                    pair(key, new_ownf),
                                                    v)))),
                      remove(cur_key,
                             map(fst, filter(engaged_cell,
                                             update(index,
                                                    pair(key, new_ownf),
                                                    v)))));
      }
    }
  }

  lemma void add_entry_preserves_msubset<kt>(list<pair<kt, int> > m,
                                             list<pair<kt, real> > v,
                                             int index,
                                             kt key,
                                             real new_ownf)
  requires true == msubset(map(fst, m), map(fst, filter(engaged_cell, v))) &*&
           0 <= index &*& index < length(v) &*&
           false == mem(key, map(fst, m)) &*&
           1.0 == snd(nth(index, v)) &*&
           0.0 < new_ownf &*& new_ownf < 1.0;
  ensures true == msubset(map(fst, map_put_fp(m, key, index)),
                          map(fst, filter(engaged_cell,
                                          update(index,
                                                 pair(key, new_ownf),
                                                 v))));
  {
    add_entry_preserves_msubset_tail(m, v, index, key, new_ownf);
    mem_update(pair(key, new_ownf), index, v);
    filter_mem(pair(key, new_ownf),
               update(index, pair(key, new_ownf), v),
               engaged_cell);
    mem_map(pair(key, new_ownf),
            filter(engaged_cell, update(index, pair(key, new_ownf), v)), fst);
    msubset_remove(map(fst, m),
                   map(fst, filter(engaged_cell,
                                   update(index, pair(key, new_ownf), v))),
                   key);
    remove_nonmem(key, map(fst,m));
  }

  lemma void mvc_coherent_put<kt>(list<pair<kt, int> > m,
                                  list<pair<kt, real> > v,
                                  dchain ch,
                                  int index, vigor_time_t time,
                                  kt key)
  requires map_vec_chain_coherent<kt>(m, v, ch) &*&
           false == dchain_allocated_fp(ch, index) &*&
           false == map_has_fp(m, key) &*&
           1.0 == snd(nth(index, v)) &*&
           0 <= index &*& index < length(v);
  ensures map_vec_chain_coherent<kt>(map_put_fp(m, key, index),
                                     update(index, pair(key, 0.75), v),
                                     dchain_allocate_fp(ch, index, time));
  {
    open map_vec_chain_coherent(m, v, ch);

    assert dchain_index_range_fp(ch) == length(v) &*&
           true == forall_idx(v, 0, (consistent_pair)(m, ch)) &*&
           true == msubset(map(fst, m), map(fst, filter(engaged_cell, v))) &*&
           map_size_fp(m) == length(dchain_indexes_fp(ch));

    allocate_preserves_index_range(ch, index, time);
    dchain_allocate_append_to_indexes(ch, index, time);
    map_has_to_mem(m, key);
    add_entry_consistent_pairs(m, v, ch, index, time, key, 0);
    add_entry_preserves_msubset(m, v, index, key, 0.75);
    close map_vec_chain_coherent(map_put_fp(m, key, index),
                                 update(index, pair(key, 0.75), v),
                                 dchain_allocate_fp(ch, index, time));
  }
  @*/

/*@
  lemma void consistent_pairs_has_key<kt>(list<pair<kt, int> > m,
                                          list<pair<kt, real> > v,
                                          dchain ch,
                                          int index,
                                          int start_idx,
                                          kt key)
  requires true == forall_idx(v, start_idx, (consistent_pair)(m, ch)) &*&
           fst(nth(index - start_idx, v)) == key &*&
           snd(nth(index - start_idx, v)) != 1.0 &*&
           0 <= start_idx &*& start_idx <= index &*&
           index - start_idx < length(v);
  ensures true == map_has_fp(m, key) &*&
          true == dchain_allocated_fp(ch, index);
  {
    switch(v) {
      case nil:
      case cons(h,t):
        if (index == start_idx) {
          switch(h) { case pair(car,cdr):}
        } else {
          consistent_pairs_has_key(m, t, ch, index, start_idx + 1, key);
        }
    }
  }
  @*/

/*@
  lemma void pairs_consistent_map_get<kt>(list<pair<kt, int> > m,
                                          list<pair<kt, real> > v, dchain ch,
                                          int index,
                                          int start_idx,
                                          kt key)
  requires true == forall_idx(v, start_idx, (consistent_pair)(m, ch)) &*&
           0 <= start_idx &*& start_idx <= index &*& index - start_idx < length(v) &*&
           fst(nth(index - start_idx, v)) == key &*&
           snd(nth(index - start_idx, v)) != 1.0;
  ensures map_get_fp(m, key) == index;
  {
    switch(v) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(cur_key,owned):
          if (index == start_idx) {
          } else {
            pairs_consistent_map_get(m, t, ch, index, start_idx + 1, key);
          }
        }
    }
  }
  @*/

/*@
  lemma void erase_unrelevant_key_consistent_pairs<kt>(list<pair<kt, int> > m,
                                                       list<pair<kt, real> > v,
                                                       dchain ch,
                                                       int index,
                                                       int start_idx,
                                                       kt key)
  requires true == forall_idx(v, start_idx, (consistent_pair)(m, ch)) &*&
           0 <= index &*& index < start_idx &*&
           true == map_has_fp(m, key) &*&
           map_get_fp(m, key) == index;
  ensures true == forall_idx(v, start_idx,
                             (consistent_pair)(map_erase_fp(m, key),
                                               dchain_remove_index_fp(ch,
                                                                      index)));
  {
    switch(v) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(cur_key, owned):
          erase_unrelevant_key_consistent_pairs(m, t, ch, index,
                                                start_idx + 1, key);
          dchain_remove_idx_from_indexes(ch, index);
          dchain_indexes_contain_index(ch, start_idx);
          dchain_indexes_contain_index(dchain_remove_index_fp(ch, index),
                                       start_idx);
          neq_mem_remove(start_idx, index, dchain_indexes_fp(ch));
          if (owned != 1.0) {
            map_erase_keeps_others(m, key, cur_key);
          }
        }
    }
  }
  @*/

/*@
  lemma void erase_entry_consistent_pairs<kt>(list<pair<kt, int> > m,
                                              list<pair<kt, real> > v,
                                              dchain ch,
                                              int index,
                                              int start_idx,
                                              kt key)
  requires true == forall_idx(v, start_idx, (consistent_pair)(m, ch)) &*&
           fst(nth(index - start_idx, v)) == key &*&
           snd(nth(index - start_idx, v)) != 1.0 &*&
           0 <= start_idx &*& start_idx <= index &*&
           index - start_idx < length(v) &*&
           true == distinct(dchain_indexes_fp(ch));
  ensures true == forall_idx(vector_erase_fp(v, index - start_idx), start_idx,
                             (consistent_pair)(map_erase_fp(m, key),
                                               dchain_remove_index_fp(ch,
                                                                      index)));
  {
    switch(v) {
      case nil:
      case cons(h,t): switch(h) { case pair(cur_key, owned):
        dchain_remove_idx_from_indexes(ch, index);
        dchain_indexes_contain_index(ch, start_idx);
        dchain_indexes_contain_index(dchain_remove_index_fp(ch, index),
                                     start_idx);
        if (index == start_idx) {
          distinct_mem_remove(index, dchain_indexes_fp(ch));
          assert true == forall_idx(t, start_idx + 1, (consistent_pair)(m, ch));
          erase_unrelevant_key_consistent_pairs(m, t, ch, index,
                                                start_idx + 1, key);
        } else {
          erase_entry_consistent_pairs(m, t, ch, index, start_idx + 1, key);
          neq_mem_remove(start_idx, index, dchain_indexes_fp(ch));
          if (owned == 1.0) {
            assert false == dchain_allocated_fp(ch, start_idx);
          } else {
            assert true == map_has_fp(m, cur_key);
            assert map_get_fp(m, cur_key) == start_idx;
            assert true == dchain_allocated_fp(ch, start_idx);

            if (key == cur_key) {
              assert map_get_fp(m, cur_key) == start_idx;
              pairs_consistent_map_get(m, v, ch, index, start_idx, key);
              assert map_get_fp(m, key) == index;
              assert index == start_idx;
            }

            map_erase_keeps_others(m, key, cur_key);
            assert true == map_has_fp(map_erase_fp(m, key), cur_key);
            assert map_get_fp(m, cur_key) == start_idx;
            assert true == dchain_allocated_fp(ch, start_idx);
          }
        }
      }
    }
  }
  @*/

/*@
  lemma void erase_key_msubset<kt>(list<pair<kt, real> > v, int index, kt key)
  requires fst(nth(index, v)) == key &*&
           snd(nth(index, v)) != 1.0;
  ensures true == msubset(filter(engaged_cell, v),
                          cons(pair(key, snd(nth(index, v))),
                               filter(engaged_cell,
                                      vector_erase_fp(v, index))));
  {
    switch(v) {
      case nil:
      case cons(h,t):
        if (index == 0) {
          msubset_refl(filter(engaged_cell, t));
          switch(h) { case pair(car,cdr): }
        } else {
          erase_key_msubset(t, index - 1, key);
        }
    }
  }
  @*/

/*@

lemma void erase_unrelevant_key_mem_engaged<kt>(list<pair<kt, real> > v,
                                                kt k, int index)
requires true == mem(k, map(fst, filter(engaged_cell, v))) &*&
         fst(nth(index, v)) != k &*&
         0 <= index;
ensures true == mem(k, map(fst, filter(engaged_cell, vector_erase_fp(v, index))));
{
  switch(v) {
    case nil:
    case cons(h,t):
      if (engaged_cell(h) && fst(h) == k) {
        return;
      } else if (0 < index) {
        erase_unrelevant_key_mem_engaged(t, k, index - 1);
      }
  }
}
@*/

/*@
  lemma void erase_unrelevant_preserves_msubset<kt>(list<kt> keys,
                                                    list<pair<kt, real> > v,
                                                    int index,
                                                    kt key)
  requires true == msubset(keys, map(fst, filter(engaged_cell, v))) &*&
           fst(nth(index, v)) == key &*&
           snd(nth(index, v)) != 1.0 &*&
           false == mem(key, keys) &*&
           0 <= index;
  ensures true == msubset(keys, map(fst, filter(engaged_cell,
                                                vector_erase_fp(v, index))));
  {
    switch(keys) {
      case nil:
      case cons(h,t):
        msubset_unremove_outer(t, map(fst, filter(engaged_cell, v)), h);
        erase_unrelevant_preserves_msubset(t, v, index, key);
        assert true == mem(h, map(fst, filter(engaged_cell, v)));
        erase_unrelevant_key_mem_engaged(v, h, index);
        assert true == mem(h, map(fst, filter(engaged_cell, vector_erase_fp(v, index))));

        assert true == msubset(t, remove(h, map(fst, filter(engaged_cell, v))));
        erase_key_msubset(v, index, key);

        msubset_map(fst,
                    filter(engaged_cell, v),
                    cons(pair(key, snd(nth(index, v))),
                         filter(engaged_cell, vector_erase_fp(v, index))));

        assert true == msubset(map(fst, filter(engaged_cell, v)),
                               cons(key, map(fst, filter(engaged_cell,
                                                         vector_erase_fp(v, index)))));

        msubset_remove(map(fst, filter(engaged_cell, v)), 
                       cons(key, map(fst, filter(engaged_cell,
                                                 vector_erase_fp(v, index)))),
                       h);
        msubset_trans(t,
                      remove(h, map(fst, filter(engaged_cell, v))),
                      cons(key,
                           remove(h, map(fst,
                                         filter(engaged_cell,
                                                vector_erase_fp(v, index))))));
        msubset_remove(t,
                       cons(key,
                            remove(h, map(fst,
                                          filter(engaged_cell,
                                                 vector_erase_fp(v, index))))),
                       key);
        remove_nonmem(key, t);
        assert true == msubset(t, remove(h,
                                          map(fst, filter(engaged_cell,
                                                vector_erase_fp(v, index)))));
        assert true == mem(h, map(fst, filter(engaged_cell, vector_erase_fp(v, index))));
        assert true == msubset(keys, map(fst, filter(engaged_cell,
                                                vector_erase_fp(v, index))));
    }
  }
  @*/

/*@
  lemma void erase_entry_preserves_msubset<kt>(list<pair<kt, int> > m,
                                               list<pair<kt, real> > v,
                                               dchain ch,
                                               int index,
                                               kt key)
  requires true == msubset(map(fst, m), map(fst, filter(engaged_cell, v))) &*&
           fst(nth(index, v)) == key &*&
           snd(nth(index, v)) != 1.0 &*&
           true == map_has_fp(m, key) &*&
           true == distinct(map(fst, m)) &*&
           0 <= index;
  ensures true == msubset(map(fst, map_erase_fp(m, key)),
                          map(fst, filter(engaged_cell,
                                          vector_erase_fp(v, index))));
  {
    switch(m) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(cur_key,cur_idx):
          msubset_unremove_outer(map(fst, t),
                                 map(fst, filter(engaged_cell, v)),
                                 cur_key);
          if (cur_key != key) {
            erase_entry_preserves_msubset(t, v, ch, index, key);
            assert true == msubset(map(fst, m),
                                   map(fst, filter(engaged_cell, v)));
            assert true == mem(cur_key, map(fst, filter(engaged_cell, v)));
            particular_mem_map_filter(cur_key, v);
            assert (true == mem(cur_key, map(fst, filter(engaged_cell, v))));
            erase_unrelevant_key_mem_engaged(v, cur_key, index);
            assert true == mem(cur_key, map(fst, filter(engaged_cell, vector_erase_fp(v, index))));
            assert false == mem(cur_key, map(fst, t));
            map_has_to_mem(t, cur_key);
            map_erase_keeps_others(t, key, cur_key);
            map_has_to_mem(map_erase_fp(t, key), cur_key);
            assert false == mem(cur_key, map(fst, map_erase_fp(t, key)));
            msubset_remove(map(fst, map_erase_fp(t, key)),
                           map(fst, filter(engaged_cell,
                                           vector_erase_fp(v, index))),
                           cur_key);
            remove_nonmem(cur_key, map(fst, map_erase_fp(t, key)));
          } else {
            assert false == mem(key, map(fst, t));
            erase_unrelevant_preserves_msubset(map(fst, t), v, index, key);
          }
        }
    }
  }
  @*/

/*@
  lemma void map_erase_size<kt>(list<pair<kt, int> > m, kt key)
  requires true;
  ensures map_size_fp(m) == map_size_fp(map_erase_fp(m, key)) +
                            (map_has_fp(m, key) ? 1 : 0);
  {
    switch(m) {
      case nil:
      case cons(h,t):
        if (fst(h) != key) map_erase_size(t, key);
    }
  }
  @*/

/*@
  lemma void vector_getf_engaged<kt>(list<pair<kt, real> > v, kt key)
  requires true;
  ensures vector_getf(filter(engaged_cell, v), key) != 1.0;
  {
    if (mem(key, map(fst, filter(engaged_cell, v)))) {
      filter_forall(engaged_cell, v);
      mem_index_of(key, map(fst, filter(engaged_cell, v)));
      map_preserves_length(fst, filter(engaged_cell, v));
      forall_nth(filter(engaged_cell, v), engaged_cell, index_of(key, map(fst, filter(engaged_cell, v))));
    }
  }
@*/

/*@
  lemma void consistent_pairs_key_index<kt>(list<pair<kt, int> > m,
                                            list<pair<kt, real> > v,
                                            dchain ch,
                                            int start_idx,
                                            kt key)
  requires true == forall_idx(v, start_idx, (consistent_pair)(m, ch)) &*&
           true == mem(key, map(fst, filter(engaged_cell, v)));
  ensures true == map_has_fp(m, key) &*&
          map_get_fp(m, key) == start_idx + index_of(pair(key, vector_getf(filter(engaged_cell, v), key)), v);
  {
    switch(v) {
      case nil:
      case cons(h,t): switch(h) { case pair(cur_key, owned):
        if (owned == 1.0) {
          consistent_pairs_key_index(m, t, ch, start_idx + 1, key);
          vector_getf_engaged(v, key);
        } else if (cur_key != key) {
          consistent_pairs_key_index(m, t, ch, start_idx + 1, key);
        }
      }
    }
  }
  @*/

/*@
  lemma void index_of_bounds<t>(t x, list<t> l)
  requires true;
  ensures 0 <= index_of(x, l) &*& index_of(x, l) <= length(l);
  {
    switch(l) {
      case nil:
      case cons(h,t):
        if (h != x) index_of_bounds(x, t);
    }
  }
@*/

/*@
  lemma void consistent_pairs_msubset_distinct<kt>(list<pair<kt, int> > m,
                                                   list<pair<kt, real> > v,
                                                   dchain ch,
                                                   int start_idx)
  requires true == forall_idx(v, start_idx, (consistent_pair)(m, ch));
  ensures true == msubset(map(fst, filter(engaged_cell, v)), map(fst, m)) &*&
          true == distinct(map(fst, filter(engaged_cell, v)));
  {
    switch(v) {
      case nil:
      case cons(h,t): switch(h) { case pair(key,owned):
        consistent_pairs_msubset_distinct(m, t, ch, start_idx + 1);
        assert true == msubset(map(fst, filter(engaged_cell, t)), map(fst, m));
        if (owned != 1.0) {
          map_has_to_mem(m, key);
          assert true == mem(key, map(fst, m));
          assert map_get_fp(m, key) == start_idx;
          if (mem(key, map(fst, filter(engaged_cell, t)))) {
            particular_mem_map_filter(key, t);
            consistent_pairs_key_index(m, t, ch, start_idx + 1, key);
            index_of_bounds(pair(key, vector_getf(filter(engaged_cell, t), key)), t);
          }
          assert false == mem(key, map(fst, filter(engaged_cell, t)));
          msubset_remove(map(fst, filter(engaged_cell, t)), map(fst, m), key);
          remove_nonmem(key, map(fst, filter(engaged_cell, t)));
        }
      }
    }
  }
  @*/

/*@
  fixpoint list<int> filter_idx2<t>(fixpoint (t,bool) f, int idx, list<t> l) {
    switch(l) {
      case nil: return nil;
      case cons(h,t):
        return (f(h)) ?
               cons(idx, filter_idx2(f, idx + 1, t)) :
               filter_idx2(f, idx + 1, t);
    }
  }
  @*/

/*@
  lemma void ge_nonmem(int x, int y, list<int> l)
  requires true == forall(l, (ge)(y)) &*& x < y;
  ensures false == mem(x, l);
  {
    switch(l) {
      case nil:
      case cons(h,t):
        ge_nonmem(x, y, t);
    }
  }
  @*/

/*@
  lemma void filter_idx2_is_distinct<t>(fixpoint (t,bool) f, int idx, list<t> l)
  requires true;
  ensures true == distinct(filter_idx2(f, idx, l)) &*&
          true == forall(filter_idx2(f, idx, l), (ge)(idx));
  {
    switch(l) {
      case nil:
      case cons(h,t):
        filter_idx2_is_distinct(f, idx + 1, t);
        if (f(h)) {
          ge_nonmem(idx, idx + 1, filter_idx2(f, idx + 1, t));
        }
        ge_le_ge(filter_idx2(f, idx + 1, t), idx + 1, idx);
    }
  }

  lemma void filter_idx2_filter_same_len<t>(fixpoint (t,bool) f,
                                           int idx,
                                           list<t> l)
  requires true;
  ensures length(filter_idx2(f, idx, l)) == length(filter(f, l));
  {
    switch(l) {
      case nil:
      case cons(h,t):
        filter_idx2_filter_same_len(f, idx + 1, t);
    }
  }
  @*/

/*@
  lemma void consistent_pairs_indexes_subset<kt>(list<pair<kt, int> > m,
                                                 list<pair<kt, real> > v,
                                                 dchain ch,
                                                 int start_idx)
  requires true == forall_idx(v, start_idx, (consistent_pair)(m, ch));
  ensures true == subset(filter_idx2(engaged_cell, start_idx, v),
                         dchain_indexes_fp(ch)) &*&
          true == subset(filter_idx2(engaged_cell, start_idx, v),
                         map(snd, m));
  {
    switch(v) {
      case nil:
      case cons(h,t): switch(h) { case pair(key,owned): }
        consistent_pairs_indexes_subset(m, t, ch, start_idx + 1);
        if (engaged_cell(h)) {
          dchain_indexes_contain_index(ch, start_idx);
          assert true == map_has_fp(m, fst(h));
          assert map_get_fp(m, fst(h)) == start_idx;
          map_get_mem(m, fst(h));
          mem_map(pair(fst(h), start_idx), m, snd);
          assert true == mem(start_idx, map(snd, m));
        }
    }
  }
  @*/

/*@
  lemma void mvc_coherent_distinct<kt>(list<pair<kt, int> > m,
                                       list<pair<kt, real> > v,
                                       dchain ch)
  requires map_vec_chain_coherent<kt>(m, v, ch);
  ensures map_vec_chain_coherent<kt>(m, v, ch) &*&
          true == distinct(dchain_indexes_fp(ch)) &*&
          true == distinct(map(fst, m)) &*&
          true == distinct(map(snd, m)) &*&
          true == distinct(map(fst, filter(engaged_cell, v))) &*&
          true == msubset(map(snd, m), dchain_indexes_fp(ch));
  {
    open map_vec_chain_coherent(m, v, ch);

    assert true == forall_idx(v, 0, (consistent_pair)(m, ch)) &*&
           true == msubset(map(fst, m), map(fst, filter(engaged_cell, v))) &*&
           map_size_fp(m) == length(dchain_indexes_fp(ch));

    consistent_pairs_msubset_distinct(m, v, ch, 0);
    assert true == msubset(map(fst, filter(engaged_cell, v)), map(fst, m));
    msubset_distinct(map(fst, m), map(fst, filter(engaged_cell, v)));
    assert true == distinct(map(fst, m));
    msubset_length(map(fst, m), map(fst, filter(engaged_cell, v)));
    msubset_length(map(fst, filter(engaged_cell, v)), map(fst, m));
    assert length(map(fst, filter(engaged_cell, v))) == length(map(fst, m));
    map_preserves_length(fst, filter(engaged_cell, v));
    map_preserves_length(fst, m);
    assert length(filter(engaged_cell, v)) == length(m);
    assert length(filter(engaged_cell, v)) == length(dchain_indexes_fp(ch));
    consistent_pairs_indexes_subset(m, v, ch, 0);
    filter_idx2_is_distinct(engaged_cell, 0, v);
    distinct_subset_msubset(filter_idx2(engaged_cell, 0, v),
                            dchain_indexes_fp(ch));
    filter_idx2_filter_same_len(engaged_cell, 0, v);
    msubset_same_len_eq(filter_idx2(engaged_cell, 0, v), dchain_indexes_fp(ch));
    msubset_distinct(dchain_indexes_fp(ch), filter_idx2(engaged_cell, 0, v));
    assert true == distinct(dchain_indexes_fp(ch));

    //assert true == msubset(dchain_indexes_fp(ch), filter_idx2(engaged_cell, 0, v));
    assert true == subset(filter_idx2(engaged_cell, 0, v), map(snd, m));
    map_preserves_length(snd, m);
    assert length(filter_idx2(engaged_cell, 0, v)) == length(map(snd, m));
    distinct_subset_msubset(filter_idx2(engaged_cell, 0, v), map(snd, m));
    msubset_same_len_eq(filter_idx2(engaged_cell, 0, v), map(snd, m));
    //assert true == msubset(dchain_indexes_fp(ch), map(snd, m));
    msubset_distinct(map(snd, m), filter_idx2(engaged_cell, 0, v));
    msubset_trans(map(snd, m), filter_idx2(engaged_cell, 0, v), dchain_indexes_fp(ch));

    close map_vec_chain_coherent(m, v, ch);
  }
  @*/

/*@
  lemma void mvc_coherent_expire_one<kt>(list<pair<kt, int> > m,
                                         list<pair<kt, real> > v,
                                         dchain ch,
                                         int index,
                                         kt key)
  requires map_vec_chain_coherent<kt>(m, v, ch)  &*&
           0 <= index &*& index < length(v) &*&
           fst(nth(index, v)) == key &*&
           snd(nth(index, v)) != 1.0;
  ensures map_vec_chain_coherent<kt>(map_erase_fp(m, key),
                                     vector_erase_fp(v, index),
                                     dchain_remove_index_fp(ch, index));
  {
    mvc_coherent_distinct(m, v, ch);
    open map_vec_chain_coherent(m, v, ch);

    dchain_remove_keeps_ir(ch, index);
    erase_entry_consistent_pairs(m, v, ch, index, 0, key);
    consistent_pairs_has_key(m, v, ch, index, 0, key);
    erase_entry_preserves_msubset(m, v, ch, index, key);
    dchain_remove_idx_from_indexes(ch, index);
    dchain_indexes_contain_index(ch, index);
    length_remove(index, dchain_indexes_fp(ch));
    map_erase_size(m, key);

    close map_vec_chain_coherent(map_erase_fp(m, key),
                                 vector_erase_fp(v, index),
                                 dchain_remove_index_fp(ch, index));
  }
  @*/

/*@
fixpoint bool synced_pair_idx<kt>(list<pair<kt, real> > keys, int start, pair<kt, uint32_t> p) {
  switch(p) {
    case pair(addr, idx):
      return 0 <= idx - start && idx - start < length(keys) &&
             engaged_cell(nth(idx - start, keys)) &&
             fst(nth(idx - start, keys)) == addr;
  }
}
@*/

/*@
lemma void map_distinct_mem_pair_get<kt,vt>(list<pair<kt,vt> > m, kt k, vt v)
requires true == distinct(map(fst, m)) &*&
         true == mem(pair(k, v), m);
ensures map_get_fp(m, k) == v;
{
  switch(m) {
    case nil:
    case cons(h,t):
      switch(h) { case pair(key, value):
        if (key == k) {
          if (value != v) {
            assert true == mem(pair(k, v), t);
            mem_map(pair(k, v), t, fst);
          }
        }
        else
          map_distinct_mem_pair_get(t, k, v);
      }
  }
}
@*/

/*@
lemma void consistent_pair_synced_pair<kt>(list<pair<kt, int> > m,
                                           list<pair<kt, real> > v,
                                           dchain ch,
                                           pair<kt, int> entry,
                                           int i)
requires true == mem(entry, m) &*&
         true == forall_idx(v, i, (consistent_pair)(m, ch)) &*&
         true == mem(fst(entry), map(fst, filter(engaged_cell, v))) &*&
         true == distinct(map(fst, m)) &*&
         true == distinct(map(snd, m)) &*&
         0 <= snd(entry) - i &*& snd(entry) - i < length(v) &*&
         1.0 != snd(nth(snd(entry) - i, v));
ensures true == synced_pair_idx(v, i, entry);
{
  switch(v) {
    case nil:
    case cons(h,t):
      switch(h) { case pair(val, owned):
        switch(entry) { case pair(addr, idx):
          if (i == idx) {
            assert 0 <= snd(entry) - i;
            assert snd(entry) - i < length(v);
            assert h == nth(idx - i, v);
            if (owned == 1.0) {
              consistent_pair_synced_pair(m, t, ch, entry, i + 1);
            } else {
              assert owned != 1.0;
              map_distinct_mem_pair_get(m, addr, idx);
              if (addr != val) {
                assert true == map_has_fp(m, val);
                assert map_get_fp(m, val) == idx;
                assert map_get_fp(m, addr) == idx;
                assert true == map_has_fp(m, val);
                mem_map(entry, m, fst);
                map_has_to_mem(m, addr);
                assert true == map_has_fp(m, addr);
                map_has_two_values_nondistinct(m, val, addr);
                assert false;
              }
            }
            return;
          } else {
            if (addr == val && owned != 1.0) {
              map_distinct_mem_pair_get(m, addr, idx);
            }
            consistent_pair_synced_pair(m, t, ch, entry, i + 1);
          }
        }
      }
  }
}
@*/

/*@
lemma void synced_pair_0<kt>(list<pair<kt, int> > m,
                             list<pair<kt, real> > v)
requires true == forall(m, (synced_pair_idx)(v, 0));
ensures true == forall(m, (synced_pair)(v));
{
  switch(m) {
    case nil:
    case cons(h,t):
      synced_pair_0(t, v);
      switch(h) { case pair(aaa,bbb): }
  }
}
@*/

/*@
lemma void drop_msubset<t>(int n, list<t> l)
requires true;
ensures true == subset(drop(n, l), l) &*&
        true == msubset(drop(n, l), l);
{
  switch(l) {
    case nil:
    case cons(h,t):
      if (0 != n) {
        drop_msubset(n - 1, t);
        msubset_cons_preserves(drop(n, l), t, h);
      } else {
        msubset_refl(l);
      }
      msubset_subset(drop(n, l), l);
  }
}
@*/

/*@
lemma void consistent_pairs_synced_pairs<kt>(list<pair<kt, int> > m,
                                             list<pair<kt, real> > v,
                                             dchain ch,
                                             list<pair<kt, int> > cur_m,
                                             int i)
requires drop(i, m) == cur_m &*&
         0 <= i &*& i + length(cur_m) == length(m) &*&
         true == forall_idx(v, 0, (consistent_pair)(m, ch)) &*&
         true == distinct(map(fst, m)) &*&
         true == distinct(map(snd, m)) &*&
         true == msubset(map(fst, m), map(fst, filter(engaged_cell, v)));
ensures true == forall(cur_m, (synced_pair_idx)(v, 0));
{
  switch(cur_m) {
    case nil:
    case cons(h,t):
      drop_msubset(i, m);
      subset_mem_trans(cur_m, m, h);
      mem_map(h, m, fst);
      msubset_subset(map(fst, m), map(fst, filter(engaged_cell, v)));
      subset_mem_trans(map(fst, m), map(fst, filter(engaged_cell, v)), fst(h));

      map_has_to_mem(m, fst(h));
      pairs_consistent_get_index(m, v, ch, fst(h), 0);
      switch(h) { case pair(aaa,bbb): }
      map_distinct_mem_pair_get(m, fst(h), snd(h));
      consistent_pair_synced_pair(m, v, ch, h, 0);
      drop_drop(1, i, m);
      consistent_pairs_synced_pairs(m, v, ch, t, i + 1);
  }
}
@*/

/*@
lemma void mvc_coherent_keys_synced<kt>(list<pair<kt, int> > m,
                                        list<pair<kt, real> > v, dchain ch)
requires map_vec_chain_coherent(m, v, ch);
ensures map_vec_chain_coherent(m, v, ch) &*&
        true == forall(m, (synced_pair)(v)) &*&
        true == msubset(map(snd, m), dchain_indexes_fp(ch));
{
  mvc_coherent_distinct(m, v, ch);
  assert true == distinct(dchain_indexes_fp(ch));
  open map_vec_chain_coherent(m, v, ch);
  assert 
    dchain_index_range_fp(ch) == length(v) &*&
    true == forall_idx(v, 0, (consistent_pair)(m, ch)) &*&
    true == msubset(map(fst, m), map(fst, filter(engaged_cell, v))) &*&
    map_size_fp(m) == length(dchain_indexes_fp(ch));

  consistent_pairs_synced_pairs(m, v, ch, m, 0);
  synced_pair_0(m, v);

  close map_vec_chain_coherent(m, v, ch);
}
@*/

/*@
lemma void synced_pairs_bounded_engaged<kt>(list<pair<kt, int> > m, list<pair<kt, real> > v)
requires true == forall(m, (synced_pair)(v));
ensures true == forall(map(snd, m), (bounded)(length(v))) &*&
        true == forall(map(snd, m), (sup)(engaged_cell, (nth2)(v)));
{
  switch(m) {
    case nil:
    case cons(h,t):
      switch(h) { case pair(key,idx):
        synced_pairs_bounded_engaged(t, v);
      }
  }
}
@*/

/*@
lemma void mvc_coherent_dchain_indexes<kt>(list<pair<kt, int> > m,
                                            list<pair<kt, real> > v,
                                            dchain ch)
requires map_vec_chain_coherent<kt>(m, v, ch);
ensures map_vec_chain_coherent<kt>(m, v, ch) &*&
        true == distinct(dchain_indexes_fp(ch)) &*&
        true == forall(dchain_indexes_fp(ch),
                      (bounded)(length(v))) &*&
        true == forall(dchain_indexes_fp(ch),
                      (sup)(engaged_cell, (nth2)(v)));
{
  mvc_coherent_distinct(m, v, ch);
  mvc_coherent_keys_synced(m, v, ch);
  open map_vec_chain_coherent(m, v, ch);
  close map_vec_chain_coherent(m, v, ch);
  map_preserves_length(snd, m);
  msubset_same_len_eq(map(snd, m), dchain_indexes_fp(ch));
  synced_pairs_bounded_engaged(m, v);
  msubset_forall(dchain_indexes_fp(ch),
                 map(snd, m),
                 (bounded)(length(v)));
  msubset_forall(dchain_indexes_fp(ch),
                 map(snd, m),
                 (sup)(engaged_cell, (nth2)(v)));

}
@*/
/*@
  lemma void mvc_coherent_map_get<kt>(list<pair<kt, int> > m,
                                      list<pair<kt, real> > v,
                                      dchain ch,
                                      kt key)
  requires map_vec_chain_coherent<kt>(m, v, ch) &*&
           true == map_has_fp(m, key);
  ensures map_vec_chain_coherent<kt>(m, v, ch) &*&
          fst(nth(map_get_fp(m, key), v)) == key;
  {
    mvc_coherent_map_get_bounded(m, v, ch, key);
    mvc_coherent_distinct(m, v, ch);
    assert true == dchain_allocated_fp(ch, map_get_fp(m, key));
    open map_vec_chain_coherent(m, v, ch);
    close map_vec_chain_coherent(m, v, ch);
    int i = map_get_fp(m, key);
    extract_prop_by_idx(v, (consistent_pair)(m, ch), 0, i);
    pair<kt, real> el = nth(i, v);
    assert true == consistent_pair(m, ch, i, el);
    switch(el) {
      case pair(car, cdr):
        map_get_mem(m, key);
        map_get_mem(m, car);
        assert true == mem(pair(key, i), m);
        assert true == mem(pair(car, i), m);
        distinct_unique(map(snd, m), i);
        unique_map_identical_elems(snd, m, pair(car, i), pair(key, i));
    }
  }
  @*/

/*@
  lemma void mvc_coherent_erase<kt>(list<pair<kt, int> > m,
                                    list<pair<kt, real> > v, dchain ch,
                                    kt key)
  requires map_vec_chain_coherent<kt>(m, v, ch) &*&
           true == map_has_fp(m, key);
  ensures map_vec_chain_coherent<kt>
            (map_erase_fp(m, key),
             update(map_get_fp(m, key), pair(key, 1.0), v),
             dchain_remove_index_fp(ch, map_get_fp(m, key)));
  {
    mvc_coherent_map_get_bounded(m, v, ch, key);
    mvc_coherent_map_get(m, v, ch, key);
    mvc_coherent_expire_one(m, v, ch, map_get_fp(m, key), key);
  }
  @*/
