//@ #include "permutations.gh"
//@ #include "listutils-lemmas.gh"

/*@

    // ------------- is_permutation -------------

    // ------------- is_sub_permutation -------------

    lemma void sub_permutation_complete(list<int> xs)
        requires    true == is_sub_permutation(xs, length(xs));
        ensures     true == is_permutation(xs);
    {}

    lemma void take_preserves_mem<t>(list<t> tail, t head, int i)
        requires    false == mem(head, tail) &*& 0 <= i;
        ensures     false == mem(head, take(i, tail));
    {
        switch(tail) {
            case nil:
            case cons(x0, xs0):
                assert (head != x0);
                if (i > 0) {
                    take_preserves_mem(xs0, head, i-1);
                }
        }
    }

    lemma void take_preserves_distinct<t>(list<t> xs, int i)
        requires    true == distinct(xs) &*& 0 <= i;
        ensures     true == distinct(take(i, xs));
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0):
                if (i > 0) {
                    take_preserves_distinct(xs0, i - 1);
                    cons_take_take_cons(x0, xs0, i - 1);
                    take_preserves_mem(xs0, x0, i - 1);
                } else {
                    take_0(xs);
                }
        }
    }

    lemma void sub_permutation_take(list<int> xs, int max_val, int i)
        requires    true == is_sub_permutation(xs, max_val) &*& 0 <= i &*& i < length(xs);
        ensures     true == is_sub_permutation(take(i, xs), max_val);
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0):
                if (i <= 0) {
                    assert (take(i, xs) == nil);
                    assert (true == is_sub_permutation(take(i, xs), max_val));
                } else {
                    sub_permutation_take(xs0, max_val, i - 1);
                    take_plus_one(i - 1, xs0);

                    cons_take_take_cons(x0, xs0, i - 1);
                    forall_append(take(i - 1, xs0), cons(x0, nil), (lt)(max_val));
                    forall_append(take(i - 1, xs0), cons(x0, nil), (ge)(max_val));
                    take_preserves_distinct(xs, i);
                }

        }
    }

    // ------------- permutations & count -------------

    lemma void mem_count_zero<t>(list<t> xs, t elem)
        requires    false == mem(elem, xs);
        ensures     count(xs, (eq)(elem)) == 0;
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0): mem_count_zero(xs0, elem);
        }
    }

    lemma void mem_count_bound<t>(list<t> xs, t elem)
        requires    true == mem(elem, xs);
        ensures     count(xs, (eq)(elem)) >= 1;
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0):
                if (x0 != elem) {
                    mem_count_bound(xs0, elem);
                } else {
                    if (mem(elem, xs0)) {
                        mem_count_bound(xs0, elem);
                    } else {
                        mem_count_zero(xs0, elem);
                    }
                }

        }
    }

    lemma void count_distinct<t>(list<t> xs, t elem)
        requires    true == distinct(xs);
        ensures     count(xs, (eq)(elem)) <= 1;
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0):
                if (x0 != elem) {
                    count_distinct(xs0, elem);
                } else {
                    assert (false == mem(elem, xs0));
                    mem_count_zero(xs0, elem);
                }

        }
    }

    lemma void permutation_exists_helper(list<int> xs, list<int> integers, int max_val, int x)
        requires
            true == is_sub_permutation(xs, max_val) &*& 0 < max_val &*&
            0 <= x &*& x < max_val &*& length(xs) == length(integers) &*&
            true == subset(xs, integers) &*& true == mem(x, integers);
        ensures
            true == mem(x, xs);
    {
        switch(xs) {
            case nil:
                length_0_nil(integers);
                assert (integers == nil);
                assert (false == mem(x, integers));
            case cons(x0, xs0):
                if (x0 == x) {
                    assert (true == mem(x, xs));
                } else {
                    remove_both_subset(x0, xs, integers);
                    neq_mem_remove(x, x0, integers);
                    permutation_exists_helper(xs0, remove(x0, integers), max_val, x);
                }
        }
    }

    lemma void permutation_exists(list<int> xs, int x)
        requires    true == is_permutation(xs) &*& 0 <= x &*& x < length(xs);
        ensures     count(xs, (eq)(x)) == 1;
    {
        list<int> integers = integers_list(nat_of_int(length(xs)), 0);
        integers_list_subset(xs, 0, length(xs));
        val_integers_list(nat_of_int(length(xs)), 0, x);
        permutation_exists_helper(xs, integers, length(xs), x);
        count_distinct(xs, x);
        mem_count_bound(xs, x);
    }

    lemma void permutation_to_count(list<int> xs, nat val)
        requires    true == is_permutation(xs) &*& 0 < length(xs) &*& int_of_nat(val) <= length(xs) - 1;
        ensures     true == integer_copies(val, 1, xs);
    {
        switch(val) {
            case zero:permutation_exists(xs, 0);
            case succ(val_pred):
                permutation_exists(xs, int_of_nat(val));
                permutation_to_count(xs, val_pred);
        }
    }

    lemma void permutation_split_to_count(list<int> xs, nat nb_split, int n)
        requires
            true == forall(split(xs, nb_split, n), is_permutation) &*&
            length(xs) == int_of_nat(nb_split) * n &*&
            0 < n &*& n <= length(xs);
        ensures
            true == integer_copies(nat_of_int(n - 1), int_of_nat(nb_split), xs);
    {
        switch(nb_split) {
            case zero:
            case succ(nb_split_pred):
                if (nb_split_pred != zero) {
                    // Recursive call
                    length_drop(n, xs);
                    mul_subst(int_of_nat(nb_split_pred) + 1, int_of_nat(nb_split), n);
                    mul_equal(n, int_of_nat(nb_split_pred), length(xs) - n);
                    permutation_split_to_count(drop(n, xs), nb_split_pred, n);
                }

                list<int> ret_xs = drop(n, xs);
                list<int> first_chunk = take(n, xs);
                assert (xs == append(first_chunk, ret_xs));

                split_chunk_equiv(xs, nb_split, n, 0);
                permutation_to_count(first_chunk, nat_of_int(length(first_chunk) - 1));
                integer_copies_append(first_chunk, ret_xs, nat_of_int(n - 1), 1, int_of_nat(nb_split_pred));
        }
    }

@*/
