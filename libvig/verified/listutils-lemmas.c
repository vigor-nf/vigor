//@ #include "listutils.gh"
//@ #include "listutils-lemmas.gh"

/*@
    // ------------- filter_idx -------------

    lemma void filter_idx_length_count_equiv<t>(list<t> xs, int idx, fixpoint (t, bool) fp)
        requires    true;
        ensures     count(xs, fp) == length(filter_idx(xs, idx, fp));
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0): filter_idx_length_count_equiv(xs0, idx + 1, fp);
        }
    }

    lemma void filter_idx_ge<t>(list<t> xs, int idx, fixpoint(t, bool) fp)
        requires    true;
        ensures     true == forall(filter_idx(xs, idx, fp), (ge)(idx));
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0):
                filter_idx_ge(xs0, idx + 1, fp);
                ge_le_ge(filter_idx(xs0, idx + 1, fp), idx + 1, idx);
        }
    }

    lemma void filter_idx_lt<t>(list<t> xs, int idx, fixpoint(t, bool) fp)
        requires    true;
        ensures     true == forall(filter_idx(xs, idx, fp), (lt)(idx + length(xs)));
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0): filter_idx_lt(xs0, idx + 1, fp);
        }
    }

    lemma void mem_ge(list<int> xs, int low_bound, int x)
        requires    true == forall(xs, (ge)(low_bound)) &*& x < low_bound;
        ensures     false == mem(x, xs);
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0):
                forall_nth(xs, (ge)(low_bound), 0);
                mem_ge(xs0, low_bound, x);
        }
    }

    lemma void filter_idx_distinct<t>(list<t> xs, int idx, fixpoint(t, bool) fp)
        requires    true;
        ensures     true == distinct(filter_idx(xs, idx, fp));
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0):
                filter_idx_distinct(xs0, idx + 1, fp);
                filter_idx_ge(xs0, idx + 1, fp);
                if (fp(x0)) {
                    mem_ge(filter_idx(xs0, idx + 1, fp), idx + 1, idx);
                }
        }
    }

    lemma void filter_idx_append<t>(list<t> xs, list<t> ys, int idx, fixpoint (t, bool) fp)
        requires    true;
        ensures     filter_idx(append(xs, ys), idx, fp) == append(filter_idx(xs, idx, fp), filter_idx(ys, idx + length(xs), fp));
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0): filter_idx_append(xs0, ys, idx + 1, fp);
        }
    }

    lemma void filter_idx_count_append<t>(list<t> xs, list<t> ys, int idx, fixpoint (t, bool) fp)
        requires    true;
        ensures     length(filter_idx(append(xs, ys), idx, fp)) == count(xs, fp) + count(ys, fp);
    {
        switch(xs) {
            case nil: filter_idx_length_count_equiv(ys, idx, fp);
            case cons(x0, xs0): filter_idx_count_append(xs0, ys, idx + 1, fp);
        }
    }

    lemma void filter_idx_drop_last<t>(list<t> xs, int idx, fixpoint(t, bool) fp, t x)
        requires    false == fp(x);
        ensures     filter_idx(xs, idx, fp) == filter_idx(append(xs, cons(x, nil)), idx, fp);
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0): filter_idx_drop_last(xs0, idx + 1, fp, x);
        }
    }

    lemma void filter_idx_include_last<t>(list<t> xs, int idx, fixpoint(t, bool) fp, t x)
        requires    true == fp(x);
        ensures     append(filter_idx(xs, idx, fp), cons(idx + length(xs), nil)) == filter_idx(append(xs, cons(x, nil)), idx, fp);
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0): filter_idx_include_last(xs0, idx + 1, fp, x);
        }
    }

    lemma void filter_idx_nth_to_mem<t>(list<t> xs, int idx, fixpoint (t, bool) fp, int i)
        requires    true == fp(nth(i, xs)) &*& 0 <= i &*& i < length(xs);
        ensures     true == mem(i + idx, filter_idx(xs, idx, fp));
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0): if (i > 0) filter_idx_nth_to_mem(xs0, idx + 1, fp, i - 1);
        }
    }

    lemma void filter_idx_mem_to_nth<t>(list<t> xs, int idx, fixpoint (t, bool) fp, int i)
        requires    true == mem(i + idx, filter_idx(xs, idx, fp)) &*& 0 <= i &*& i < length(xs);
        ensures     true == fp(nth(i, xs));
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0):
                if (i > 0) filter_idx_mem_to_nth(xs0, idx + 1, fp, i - 1);
                else {
                    filter_idx_ge(xs0, idx + 1, fp);
                    if (!fp(x0)) {
                        assert (filter_idx(xs, idx, fp) == filter_idx(xs0, idx + 1, fp));
                        assert (true == mem(idx, filter_idx(xs, idx, fp)));
                        assert (true == forall(filter_idx(xs, idx, fp), (ge)(idx + 1)));
                        mem_ge(filter_idx(xs, idx, fp), idx + 1, idx);
                    }
                }
        }
    }

    lemma void count_idx<t>(list<t> xs, fixpoint(t, bool) fp, int i)
        requires    true == fp(nth(i, xs)) &*& 0 <= i &*& i < length(xs);
        ensures     count(xs, fp) > 0;
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0):
                if (i > 0) {
                    count_idx(xs0, fp, i - 1);
                } else {
                    count_nonnegative(xs0, fp);
                }
        }
    }

    lemma void filter_idx_fst<t>(list<t> xs, int idx, fixpoint (t, bool) fp, int i)
        requires    count(take(i, xs), fp) == 0 &*& true == fp(nth(i, xs)) &*& 0 <= i &*& i < length(xs);
        ensures     nth(0, filter_idx(xs, idx, fp)) == i + idx;
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0):
                if (i > 0) {
                    count_nonnegative(take(i - 1, xs0), fp);
                    filter_idx_fst(xs0, idx + 1, fp, i - 1);
                }
        }
    }

    lemma void filter_idx_take<t>(list<t> xs, int idx, fixpoint (t, bool) fp, int count, int i)
        requires
            count(take(i, xs), fp) == count &*& true == fp(nth(i, xs)) &*&
            0 <= count &*& 0 <= i &*& i < length(xs);
        ensures
            nth(count, filter_idx(xs, idx, fp)) == i + idx;
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0):
                if (i > 0) {
                    if (fp(x0)) {
                        count_idx(take(i, xs), fp, 0);
                        filter_idx_take(xs0, idx + 1, fp, count - 1, i - 1);
                    } else {
                        if (count == 0) {
                            filter_idx_fst(xs, idx, fp, i);
                        } else {
                            filter_idx_take(xs0, idx + 1, fp, count, i - 1);
                        }
                    }
                }
        }
    }

    // ------------- index_of_fixpoint -------------

    lemma void index_of_fp_exists<t>(list<t> xs, int idx, fixpoint (t,bool) fp, int i)
        requires    true == forall(take(i, xs), (sup)((eq)(false), fp)) &*& true == fp(nth(i, xs)) &*& 0 <= i &*& i < length(xs);
        ensures     index_of_fp(xs, idx, fp) == some(idx + i);
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0): if (i > 0) index_of_fp_exists(xs0, idx + 1, fp, i - 1);
        }
    }

    // ------------- integer_copies -------------

    lemma_auto(integer_copies(val, nb_copies, nil)) void integer_copies_nil(nat val, int nb_copies)
        requires    0 == nb_copies;
        ensures     true == integer_copies(val, nb_copies, nil);
    {
        switch(val) {
            case zero:
            case succ(val_pred): integer_copies_nil(val_pred, nb_copies);
        }
    }

    lemma void integer_copies_val(int x, nat val, int nb_copies, list<int> xs)
        requires    true == integer_copies(val, nb_copies, xs) &*& 0 <= x &*& x <= int_of_nat(val);
        ensures     count(xs, (eq)(x)) == nb_copies;
    {
        switch(val) {
            case zero:
            case succ(val_pred):
                if (int_of_nat(val) != x) {
                    integer_copies_val(x, val_pred, nb_copies, xs);
                }
        }
    }

    lemma void integer_copies_append(list<int> xs, list<int> ys, nat val, int nb_copies_xs, int nb_copies_ys)
        requires    true == integer_copies(val, nb_copies_xs, xs) &*& true == integer_copies(val, nb_copies_ys, ys);
        ensures     true == integer_copies(val, nb_copies_xs + nb_copies_ys, append(xs, ys));
    {
        switch(val) {
            case zero:
                integer_copies_val(int_of_nat(val), val, nb_copies_xs, xs);
                integer_copies_val(int_of_nat(val), val, nb_copies_ys, ys);
                count_append(xs, ys, (eq)(int_of_nat(val)));
            case succ(val_pred):
                integer_copies_val(int_of_nat(val), val, nb_copies_xs, xs);
                integer_copies_val(int_of_nat(val), val, nb_copies_ys, ys);
                count_append(xs, ys, (eq)(int_of_nat(val)));
                integer_copies_append(xs, ys, val_pred, nb_copies_xs, nb_copies_ys);
        }
    }

    // ------------- flatten -------------

    lemma void flatten_allnil<t>(list< list<t> > xs)
        requires    true == forall(xs, (eq)(nil));
        ensures     flatten(xs) == nil;
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0): flatten_allnil(xs0);
        }
    }

    // ------------- chunk -------------

    lemma void chunk_zerosize<t>(list<t> xs, int n)
        requires true;
        ensures chunk(xs, n, n) == nil;
    {
        take_0(drop(n, xs));
    }

    lemma_auto(length(chunk(xs, begin, end))) void chunk_length<t>(list<t> xs, int begin, int end)
        requires    0 <= begin && begin <= end && end <= length(xs);
        ensures     length(chunk(xs, begin, end)) == end - begin;
    {
        length_drop(begin, xs);
        length_take(end - begin, drop(begin, xs));
    }

    lemma void chunk_shift<t>(list<t> xs, int begin, int end, int n)
        requires    0 <= begin &*& 0 <= n &*& n <= begin &*& begin + n <= length(xs);
        ensures     chunk(xs, begin, end) == chunk(drop(n, xs), begin - n, end - n);
    {
        drop_drop(begin - n, n, xs);
    }

    lemma void chunk_append<t>(list<t> xs, int begin, int end)
        requires    0 <= begin &*& begin <= end &*& end < length(xs);
        ensures     chunk(xs, begin, end + 1) == append(chunk(xs, begin, end), cons(nth(end, xs), nil));
    {
        length_drop(begin, xs);
        take_plus_one(end - begin, drop(begin, xs));
        nth_drop(end - begin, begin, xs);
    }

    lemma void chunk_take<t>(list<t> xs, int begin, int end1, int end2)
        requires    0 <= begin &*& begin <= end1 &*& end1 <= end2 &*& end2 <= length(xs);
        ensures     take(end1 - begin, chunk(xs, begin, end2)) == chunk(xs, begin, end1);
    {
        take_take(end1 - begin, end2 - begin, drop(begin, xs));
    }

    lemma void chunk_to_source<t>(list<t> xs, int begin, int end, int i)
        requires    0 <= begin &*& begin <= end &*& end <= length(xs) &*& 0 <= i &*& i < end - begin;
        ensures     nth(begin + i, xs) == nth(i, chunk(xs, begin, end));
    {
        if (begin == 0) {
            nth_take(i, end, xs);
        } else {
            length_drop(begin, xs);
            nth_drop(i, begin, xs);
        }

    }

    lemma void chunk_update_unrelevant<t>(list<t> xs, int begin, int end, int i, t val)
        requires    0 <= begin &*& begin <= end &*& end <= i &*& i < length(xs);
        ensures     chunk(xs, begin, end) == chunk(update(i, val, xs), begin, end);
    {
        drop_update_relevant(begin, i, val, xs);
        take_update_unrelevant(end - begin, i - begin, val, drop(begin, xs));
    }

    // ------------- repeat -------------

    lemma_auto(length(repeat(elem, n))) void length_repeat<t>(t elem, nat n)
        requires    true;
        ensures     length(repeat(elem, n)) == int_of_nat(n);
    {
        switch(n) {
            case zero:
            case succ(n_pred): length_repeat(elem, n_pred);
        }
    }

    lemma void repeat_content<t>(t elem, nat n)
        requires    true;
        ensures     true == forall(repeat(elem, n), (eq)(elem));
    {
        switch(n) {
            case zero:
            case succ(n_pred): repeat_content(elem, n_pred);
        }
    }

    lemma void repeat_add<t>(t elem, nat n)
        requires    n == succ(?n_pred);
        ensures     cons(elem, repeat(elem, n_pred)) == repeat(elem, n);
    {
        switch(n) {
            case zero:
            case succ(n_pred_bis):
        }
    }

    lemma void repeat_nth<t>(t elem, nat n, int i)
        requires    0 <= i &*& i < int_of_nat(n);
        ensures     nth(i, repeat(elem, n)) == elem;
    {
        repeat_content(elem, n);
        forall_nth(repeat(elem, n), (eq)(elem), i);
    }

    lemma void repeat_tail<t>(t elem, nat n)
        requires    n == succ(?n_pred);
        ensures     tail(repeat(elem, n)) == repeat(elem, n_pred);
    {}

    lemma void repeat_append<t>(t elem, nat n)
        requires    true;
        ensures     append(repeat(elem, n), cons(elem, nil)) == repeat(elem, succ(n));
    {
        switch(n) {
            case zero:
            case succ(n_pred):
              repeat_append(elem, n_pred);
        }
    }

    // ------------- split_varlim -------------

    lemma_auto(length(split_varlim(xs, n, limits))) void length_split_varlim<t>(list<t> xs, int n, list<int> limits)
        requires    length(xs) == length(limits) * n && 0 <= n;
        ensures     length(split_varlim(xs, n, limits)) == length(limits);
    {
        switch(limits) {
            case nil:
            case cons(l0, ls0):
                mul_equal(n, length(limits), length(xs));
                length_drop(n, xs);
                mul_subst (length(ls0), length(limits) - 1, n);
                length_split_varlim(drop(n, xs), n, ls0);
        }
    }

    lemma void split_varlim_nolim<t>(list<t> xs, int n, list<int> limits)
        requires
            true == forall(limits, (eq)(0)) &*&
            0 <= n &*& n * length(limits) == length(xs);
        ensures
            true == forall(split_varlim(xs, n, limits), (eq)(nil));
    {
        switch(limits) {
            case nil:
                assert (length(xs) == 0);
            case cons(l0, ls0):
                mul_equal(n, length(limits), length(xs));
                length_drop(n, xs);
                mul_subst (length(ls0), length(limits) - 1, n);
                split_varlim_nolim(drop(n, xs), n, ls0);
        }
    }

    lemma void split_varlim_chunk_equiv<t>(list<t> xs, int n, list<int> limits, int j)
        requires    0 <= n &*& 0 <= j &*& j < length(limits) &*& n * (j+1) <= length(xs) ;
        ensures     nth(j, split_varlim(xs, n, limits)) == chunk(xs, n * j, n * j + nth(j, limits));
    {
        switch(limits) {
            case nil:
            case cons(l0, ls0):
                if (j > 0) {
                    split_varlim_chunk_equiv(drop(n, xs), n, ls0, j - 1);
                    mul_nonnegative(n, j);
                    mul_bounds(1, j, n, n);
                    chunk_shift(xs, n * j, n * j + nth(j, limits), n);
                }
        }
    }

    lemma void split_varlim_update<t>(list<t> xs, int n, list<int> limits1, list<int> limits2, int i)
        requires
            0 <= i &*& i < length(limits1) &*&
            limits2 == update(i, nth(i, limits2), limits1) &*&
            nth(i, limits1) != nth(i, limits2);
        ensures
            split_varlim(xs, n, limits2) == update(i, nth(i, split_varlim(xs, n, limits2)), split_varlim(xs, n, limits1));
    {
        switch(limits1) {
            case nil:
            case cons(l0, ls0):
                if (i > 0) {
                    split_varlim_update(drop(n, xs), n, ls0, tail(limits2), i - 1);
                }
        }
    }

    lemma void split_varlim_update_unrelevant<t>(list<t> xs1, list<t> xs2, list<int> limits, int n, int i, int j, t new_val)
        requires
            xs2 == update(n * j + i, new_val, xs1) &*& nth(n * j + i, xs2) == new_val &*& nth(j, limits) <= i &*&
            true == forall(limits, (ge)(0)) &*& true == forall(limits, (le)(n)) &*&
            length(xs1) == n * length(limits) &*&
            0 <= i &*& i < n &*&
            0 <= j &*& j < length(limits);
        ensures
            split_varlim(xs1, n, limits) == split_varlim(xs2, n, limits);
    {
        switch(limits) {
            case nil:
            case cons(l0, ls0):
                if (j > 0) {
                    mul_bounds(n, n, 1, j);
                    mul_bounds(n, n, j + 1, length(limits));
                    assert(n * j + i <= n * (j + 1) - 1);
                    assert (n * (j+1) - 1 < length(xs1));
                    assert (n * j + i < length(xs1));

                    drop_update_relevant(n, n * j + i, new_val, xs1);
                    nth_drop(n * j + i - n, n, xs2);
                    length_drop(n, xs1);
                    assert( length(ls0) == length(limits) - 1);
                    mul_subst(length(ls0), length(limits) - 1, n);
                    split_varlim_update_unrelevant(drop(n, xs1), drop(n, xs2), ls0, n, i, j - 1, new_val);

                    take_update_unrelevant(l0, n * j + i, new_val, xs1);
                } else {
                    take_update_unrelevant(l0, i, new_val, xs1);
                    drop_update_unrelevant(n, i, new_val, xs1);
                }
        }
    }

    lemma void split_varlim_split_equiv<t>(list<t> xs, list<int> limits, int n, nat nb_split)
        requires    true == forall(limits, (eq)(n)) &*& length(limits) == int_of_nat(nb_split);
        ensures     split_varlim(xs, n, limits) == split(xs, nb_split, n);
    {
        switch(limits) {
            case nil:
            case cons(l0, ls0):
                forall_nth(limits, (eq)(n), 0);
                switch(nb_split) {
                    case zero:
                    case succ(nb_split_pred): split_varlim_split_equiv(drop(n, xs), ls0, n, nb_split_pred);
                }
        }
    }

    // ------------- split -------------

    lemma_auto(length(split(xs, nb_split, n))) void length_split<t>(list<t> xs, nat nb_split, int n)
        requires    length(xs) == int_of_nat(nb_split) * n && 0 <= n;
        ensures     length(split(xs, nb_split, n)) == int_of_nat(nb_split);
    {
        switch(nb_split) {
            case zero:
            case succ(nb_split_pred):
                mul_mono(1, int_of_nat(nb_split), n);
                length_drop(n, xs);
                mul_subst(int_of_nat(nb_split_pred) + 1, int_of_nat(nb_split), n);
                length_split(drop(n, xs), nb_split_pred, n);
        }
    }

    lemma_auto(length(nth(i, split(xs, nb_split, n)))) void length_split_nth<t>(list<t> xs, nat nb_split, int n, int i)
        requires    length(xs) == int_of_nat(nb_split) * n && 0 <= n && 0 <= i && i < int_of_nat(nb_split);
        ensures     length(nth(i, split(xs, nb_split, n))) == n;
    {
        switch(nb_split) {
            case zero:
            case succ(nb_split_pred):
                mul_mono(1, int_of_nat(nb_split), n);
                if (i > 0) {
                    length_drop(n, xs);
                    mul_subst(int_of_nat(nb_split_pred) + 1, int_of_nat(nb_split), n);
                    length_split_nth(drop(n, xs), nb_split_pred, n, i - 1);
                }
        }
    }

    lemma void length_split_forall<t>(list<t> xs, nat nb_split, int n)
        requires    length(xs) == int_of_nat(nb_split) * n &*& 0 <= n &*& n <= length(xs);
        ensures     true == forall(split(xs, nb_split, n), (length_eq)(n));
    {
        switch(nb_split) {
            case zero:
            case succ(nb_split_pred):
                if (nb_split_pred != zero) {
                    length_drop(n, xs);
                    mul_subst(int_of_nat(nb_split_pred) + 1, int_of_nat(nb_split), n);
                    mul_equal(n, int_of_nat(nb_split_pred), length(xs) - n);
                    length_split_forall(drop(n, xs), nb_split_pred, n);
                }
        }
    }

    lemma void split_chunk_equiv<t>(list<t> xs, nat nb_split, int n, int i)
        requires    0 < n &*& 0 <= i &*& i < int_of_nat(nb_split) &*& n * (i+1) <= length(xs);
        ensures     nth(i, split(xs, nb_split, n)) == chunk(xs, n * i, n * (i+1));
    {
        switch(nb_split) {
            case zero:
            case succ(nb_split_pred):
                if (i > 0) {
                    split_chunk_equiv(drop(n, xs), nb_split_pred, n, i-1);
                    mul_nonnegative(n, i);
                    mul_bounds(1, i, n, n);
                    chunk_shift(xs, n * i, n * (i+1), n);
                }
        }
    }

    lemma void split_to_source<t>(list<t> xs, nat nb_split, int n, int i, int j)
        requires    length(xs) == int_of_nat(nb_split) * n &*& 0 <= n &*&
                    0 <= i &*& i < n &*&
                    0 <= j &*& j < int_of_nat(nb_split);
        ensures     nth(i, nth(j, split(xs, nb_split, n))) == nth(j * n + i, xs);
    {
        mul_mono(j + 1, int_of_nat(nb_split), n);
        split_chunk_equiv(xs, nb_split, n, j);
        mul_nonnegative(j, n);
        chunk_to_source(xs, n * j, n * (j+1), i);
    }

    lemma void split_append<t>(list<t> xs, nat nb_split, int n)
        requires    int_of_nat(succ(nb_split)) * n <= length(xs) &*& 0 < n;
        ensures     split(xs, succ(nb_split), n) == append(split(xs, nb_split, n), cons(chunk(xs, n * int_of_nat(nb_split), n * (int_of_nat(nb_split) + 1)), nil));
    {
        switch(nb_split) {
            case zero:
                split_chunk_equiv(xs, succ(nb_split), n, 0);
            case succ(nb_split_pred):
                mul_mono_strict(1, int_of_nat(succ(nb_split)), n);
                length_drop(n, xs);
                mul_subst(int_of_nat(nb_split) + 1, int_of_nat(succ(nb_split)), n);
                split_append(drop(n, xs), nb_split_pred, n);

                mul_bounds(1, int_of_nat(nb_split), n, n);
                chunk_shift(xs, n * int_of_nat(nb_split), n * (int_of_nat(nb_split) + 1), n);
        }
    }

    lemma void split_update_unrelevant<t>(list<t> xs, nat nb_split, int n, int i, t val)
        requires    0 < n &*& int_of_nat(nb_split) * n <= i &*& i < length(xs);
        ensures     split(xs, nb_split, n) == split(update(i, val, xs), nb_split, n);
    {
        switch(nb_split) {
            case zero:
            case succ(nb_split_pred):
                if (nb_split_pred != zero) {
                    mul_mono_strict(1, int_of_nat(nb_split), n);
                    length_drop(n, xs);
                    mul_subst(int_of_nat(nb_split_pred) + 1, int_of_nat(nb_split), n);
                    drop_update_relevant(n, i, val, xs);
                    take_update_unrelevant(n, i, val, xs);
                    split_update_unrelevant(drop(n, xs), nb_split_pred, n, i - n, val);
                } else {
                    take_update_unrelevant(n, i, val, xs);
                }
        }
    }

    // ------------- integers_list -------------

    lemma_auto(length(integers_list(cnt, index))) void length_integers_list(nat cnt, int index)
        requires    true;
        ensures     length(integers_list(cnt, index)) == int_of_nat(cnt);
    {
        switch(cnt) {
            case zero:
            case succ(cnt_pred): length_integers_list(cnt_pred, index + 1);
        }
    }

    lemma_auto(nth(i, integers_list(cnt, index))) void val_integers_list(nat cnt, int index, int i)
        requires    0 <= i && i <  int_of_nat(cnt);
        ensures     nth(i, integers_list(cnt, index)) == index + i;
    {
        switch(cnt) {
            case zero:
            case succ(cnt_pred): if (i > 0) val_integers_list(cnt_pred, index + 1, i - 1);
        }
    }

    lemma void integers_list_bounds(nat cnt, int index)
        requires    true;
        ensures     true == forall(integers_list(cnt, index), (ge)(index)) &*& true == forall(integers_list(cnt, index), (lt)(index + int_of_nat(cnt)));
    {
        switch(cnt) {
            case zero:
            case succ(cnt_pred):
                integers_list_bounds(cnt_pred, index + 1);
                ge_le_ge(integers_list(cnt_pred, index + 1), index + 1, index);
        }
    }

    lemma void integers_list_append(nat cnt1, nat cnt2, int index)
        requires    true;
        ensures     integers_list( nat_of_int( int_of_nat(cnt1) + int_of_nat(cnt2) ) , index) == append( integers_list(cnt1, index) , integers_list(cnt2, index + int_of_nat(cnt1)));
    {
        switch(cnt1) {
            case zero:
            case succ(cnt1_pred):
                integers_list_append(cnt1_pred, cnt2, index + 1);
                assert (int_of_nat(cnt1) + int_of_nat(cnt2) == int_of_nat(cnt1_pred) + int_of_nat(cnt2) + 1);
                assert (nat_of_int(int_of_nat(cnt1) + int_of_nat(cnt2)) == succ(nat_of_int(int_of_nat(cnt1_pred) + int_of_nat(cnt2))));
        }
    }

    lemma void integers_list_distinct(nat cnt, int index)
        requires    true;
        ensures     true == distinct(integers_list(cnt, index));
    {
        switch(cnt) {
            case zero:
            case succ(cnt_pred):
                integers_list_distinct(cnt_pred, index + 1);
                integers_list_bounds(cnt_pred, index + 1);
                distinct_ge(integers_list(cnt_pred, index + 1), index + 1, index);
        }
    }

    lemma void integers_list_subset(list<int> xs, int low_bound, int up_bound)
        requires    true == forall(xs, (ge)(low_bound)) &*& true == forall(xs, (lt)(up_bound)) &*& low_bound <= up_bound;
        ensures     true == subset(xs, integers_list(nat_of_int(up_bound - low_bound), low_bound));
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0):
                integers_list_subset(xs0, low_bound, up_bound);
                forall_nth(xs, (ge)(low_bound), 0);
                forall_nth(xs, (lt)(up_bound), 0);
                val_integers_list(nat_of_int(up_bound - low_bound), low_bound, x0 - low_bound);
        }
    }

    // ------------- zip -------------

    lemma_auto(length(zip(xs, ys))) void length_zip<t1, t2>(list<t1> xs, list<t2> ys)
        requires    length(xs) == length(ys);
        ensures     length(zip(xs, ys)) == length(xs);
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0):
                switch(ys) {
                    case nil:
                    case cons(y0, ys0): length_zip(xs0, ys0);
                }
        }
    }

    lemma_auto(nth(i, zip(xs, ys))) void val_zip<t1, t2>(list<t1> xs, list<t2> ys, int i)
        requires    0 <= i && i < length(xs) && length(xs) == length(ys);
        ensures     nth(i, zip(xs, ys)) == pair(nth(i, xs), nth(i, ys));
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0):
                switch(ys) {
                    case nil:
                    case cons(y0, ys0): if (i > 0) val_zip(xs0, ys0, i - 1);
                }
        }
    }

    lemma void zip_unzip_fst<t1, t2>(list<t1> xs, list<t2> ys)
        requires    length(xs) == length(ys);
        ensures     xs == map(fst, zip(xs, ys));
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0):
                switch(ys) {
                    case nil:
                    case cons(y0, ys0): zip_unzip_fst(xs0, ys0);
                }
        }
    }

    lemma void zip_unzip_snd<t1, t2>(list<t1> xs, list<t2> ys)
        requires    length(xs) == length(ys);
        ensures     ys == map(snd, zip(xs, ys));
    {
        switch(xs) {
            case nil: length_0_nil(ys);
            case cons(x0, xs0):
                switch(ys) {
                    case nil:
                    case cons(y0, ys0): zip_unzip_snd(xs0, ys0);
                }
        }
    }

    lemma void zip_append<t1, t2>(list<t1> xs1, list<t2> ys1, list<t1> xs2, list<t2> ys2)
        requires    length(xs1) == length(ys1) &*& length(xs2) == length(ys2);
        ensures     zip(append(xs1, xs2), append(ys1, ys2)) == append(zip(xs1, ys1), zip(xs2, ys2));
    {
        switch(xs1) {
            case nil: length_0_nil(ys1);
            case cons(x0, xs0):
                switch(ys1) {
                    case nil:
                    case cons(y0, ys0): zip_append(xs0, ys0, xs2, ys2);
                }
        }
    }

    // ------------- zip_index -------------

    lemma_auto(length(zip_index(xs, idx))) void length_zip_index<t>(list<t> xs, int idx)
        requires    true;
        ensures     length(zip_index(xs, idx)) == length(xs);
    {
        length_zip(integers_list(nat_of_int(length(xs)), 0) , xs);
    }

    lemma_auto(nth(i, zip_index(xs, idx))) void val_zip_index<t>(list<t> xs, int idx, int i)
        requires    0 <= i && i < length(xs);
        ensures     nth(i, zip_index(xs, idx)) == pair(i + idx, nth(i, xs));
    {
        val_zip(integers_list(nat_of_int(length(xs)), 0) , xs, i);
        val_integers_list(nat_of_int(length(xs)), idx, i);
    }

    lemma void zip_index_unzip<t>(list<t> xs, int idx)
        requires    true;
        ensures     xs == map(snd, zip_index(xs, idx));
    {
        zip_unzip_snd(integers_list(nat_of_int(length(xs)), idx), xs);
    }

    lemma void zip_index_append<t>(list<t> xs, list<t> ys)
        requires    true;
        ensures     zip_index(append(xs, ys), 0) == append(zip_index(xs, 0), zip_index(ys, length(xs)));
    {
        integers_list_append(nat_of_int(length(xs)), nat_of_int(length(ys)), 0);
        zip_append(integers_list(nat_of_int(length(xs)), 0), xs, integers_list(nat_of_int(length(ys)), length(xs)), ys);
    }

    lemma void zip_index_bounds<t>(list<t> xs, int idx)
        requires    true;
        ensures     true == forall( map(fst, zip_index(xs, idx)), (ge)(idx) ) &*& true == forall( map(fst, zip_index(xs, idx)), (lt)(idx + length(xs)) );
    {
        zip_unzip_fst(integers_list(nat_of_int(length(xs)), idx) , xs);
        integers_list_bounds(nat_of_int(length(xs)), idx);
    }

    lemma void zip_index_distinct<t>(list<t> xs, int idx)
        requires    true;
        ensures     true == distinct(map(fst, zip_index(xs, idx)));
    {
        zip_unzip_fst(integers_list(nat_of_int(length(xs)), idx) , xs);
        integers_list_distinct(nat_of_int(length(xs)), idx);
    }

@*/
