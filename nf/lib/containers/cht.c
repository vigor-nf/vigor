#include "cht.h"
#include <assert.h>
#include <stdlib.h>

//@ #include "prime.gh"
//@ #include "permutations.gh"
//@ #include "transpose.gh"

static uint64_t loop(uint64_t k, uint64_t capacity)
//@ requires    0 < capacity &*& capacity < INT_MAX;
//@ ensures     0 <= result &*& result < capacity &*& result == k%capacity;
{
    uint64_t g = k % capacity;
    //@ div_mod_gt_0(g, k, capacity);
    return g;
}

/*@
    // ------------- 1st double-nested loop -------------


    fixpoint bool is_modulo_permutation(int offset, int shift, int cht_height, pair<int, int> index_elem_pair) {
        return snd(index_elem_pair) == ((offset + shift * fst(index_elem_pair)) % cht_height);
    }

    lemma void modulo_permutation_list_inner(list< pair<int,int> > xs, pair<int,int> index_val, int offset, int shift, int cht_height)
        requires
            true == forall(xs, (is_modulo_permutation)(offset, shift, cht_height)) &*&
            true == is_modulo_permutation(offset, shift, cht_height, index_val) &*&
            true == forall(map(fst, xs), (lt)(cht_height)) &*&
            true == forall(map(fst, xs), (ge)(0)) &*&
            true == forall(map(snd, xs), (lt)(cht_height)) &*&
            true == forall(map(snd, xs), (ge)(0)) &*&
            true == !mem(fst(index_val), map(fst, xs) ) &*&
            0 <= fst(index_val) &*& fst(index_val) < cht_height &*&
            0 <= offset &*& offset < cht_height &*&
            0 <= shift &*& shift < cht_height &*&
            0 < cht_height &*& true == are_coprime(shift, cht_height);
        ensures
            !mem(snd(index_val), map(snd, xs));
        {
            switch(xs) {
                case nil:
                    assert (true == !mem(snd(index_val), map(snd, xs)));

                case cons(x0, xs0):
                    int ref_index = fst(index_val);
                    int head_index = fst(x0);

                    // Prove that the reference is different than the head
                    modulo_permutation(shift, cht_height, ref_index, head_index);
                    mul_nonnegative(shift, ref_index);
                    div_mod_gt_0((shift * ref_index) % cht_height, shift * ref_index, cht_height);
                    mul_nonnegative(shift, head_index);
                    div_mod_gt_0((shift * head_index) % cht_height, shift * head_index, cht_height);
                    modulo_add_constant(offset, cht_height, shift * ref_index, shift * head_index);

                    // Recursive call
                    modulo_permutation_list_inner(xs0, index_val, offset, shift, cht_height);
            }
        }

    lemma void modulo_permutation_list(list< pair<int,int> > xs, int offset, int shift, int cht_height)
        requires
            true == forall(xs, (is_modulo_permutation)(offset, shift, cht_height)) &*&
            true == forall(map(fst, xs), (lt)(cht_height)) &*&
            true == forall(map(fst, xs), (ge)(0)) &*&
            true == forall(map(snd, xs), (lt)(cht_height)) &*&
            true == forall(map(snd, xs), (ge)(0)) &*&
            true == no_dups(map(fst, xs)) &*&
            0 <= offset &*& offset < cht_height &*&
            0 <= shift &*& shift < cht_height &*&
            0 < cht_height &*& true == are_coprime(shift, cht_height);
        ensures
            true == no_dups(map(snd, xs));
    {
        switch(xs) {
                case nil:
                    assert map(snd, xs) == nil;
                    assert (true == no_dups(map(snd, xs)));
                case cons(x0, xs0):
                    modulo_permutation_list(xs0, offset, shift, cht_height);
                    modulo_permutation_list_inner(xs0, x0, offset, shift, cht_height);
        }
    }

    lemma void lt_transitive(list<int> xs, int bound, int up_bound)
        requires bound <= up_bound &*& true == forall(xs, (lt)(bound));
        ensures true == forall(xs, (lt)(up_bound));
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0): lt_transitive(xs0, bound, up_bound);
        }
    }

    lemma void forall_lt_upper(list<int> xs, int up_bound, int x)
        requires true == forall(xs, (lt)(up_bound)) &*& up_bound <= x ;
        ensures !mem(x, xs);
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0): forall_lt_upper(xs0, up_bound, x);
        }
    }

    lemma void no_dups_gt(list<int> xs, int up_bound, int x)
        requires true == no_dups(xs) &*& true == forall(xs, (lt)(up_bound)) &*& up_bound <= x ;
        ensures true == no_dups(cons(x, xs));
    {
        forall_lt_upper(xs, up_bound, x);
    }

    lemma void modulo_permutation_bounds(list< pair<int, int> > xs, int offset, int shift, int cht_height)
        requires
            true == forall(xs, (is_modulo_permutation)(offset, shift, cht_height)) &*&
            true == forall(map(fst, xs), (ge)(0)) &*&
            0 <= offset &*& offset < cht_height &*&
            0 <= shift &*& shift < cht_height &*&
            0 < cht_height;
        ensures
            true == forall(map(snd, xs), (lt)(cht_height)) &*&
            true == forall(map(snd, xs), (ge)(0));
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0):
                mul_nonnegative(shift, fst(x0));
                div_mod_gt_0( (offset + shift * fst(x0)) % cht_height, offset + shift * fst(x0), cht_height);
                modulo_permutation_bounds(xs0, offset, shift, cht_height);
        }
    }

    // ------------- 2nd double-nested loop -------------

    lemma void bounds_from_eq(list<int> xs, int x, int up_bound)
        requires    true == forall(xs, (eq)(x)) &*& x <= up_bound;
        ensures     true == forall(xs, (le)(up_bound)) &*& true == forall(xs, (ge)(x));
    {
        switch(xs){
            case nil:
            case cons(x0, xs0): bounds_from_eq(xs0, x, up_bound);
        }
    }

    fixpoint bool next_from_permuts(list<int> xs, int bucket_id, int next_elem) {
        return next_elem == count(xs, (eq)(bucket_id));
    }

    lemma void next_from_permuts_init(list<int> ns, int idx)
        requires    true == forall(ns, (eq)(0));
        ensures     true == forall_idx(ns, idx, (next_from_permuts)(nil));
    {
        switch(ns) {
            case nil:
            case cons(n0, ns0):
                assert (count(nil, (eq)(idx)) == 0);
                next_from_permuts_init(ns0, idx + 1);
        }
    }

    lemma void next_from_permuts_end(list<int> ns, int idx, nat val, int nb_copies, list<int> xs)
        requires
            true == forall_idx(ns, idx, (next_from_permuts)(xs)) &*&
            true == integer_copies(val, nb_copies, xs) &*&
            0 <= idx &*& idx + length(ns) - 1 == int_of_nat(val);
        ensures
            true == forall(ns, (eq)(nb_copies));
    {
        switch(ns) {
            case nil:
            case cons(n0, ns0):
                next_from_permuts_end(ns0, idx + 1, val, nb_copies, xs);
                integer_copies_val(idx, val, nb_copies, xs);
        }
    }

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

    lemma void next_from_permuts_update(list<int> next, list<int> next_update, int idx, list< list<int> > xs, list< list<int> > ys, list<int> xs_elem, list<int> ys_elem, nat val, int i, int j, int special_value)
        requires
            true == forall_idx(next, idx, (next_from_permuts)(flatten(xs))) &*&
            true == forall(next_update, (ge)(0)) &*&
            j < length(next) &*& length(next) <= int_of_nat(val) + 1 &*&
            idx == int_of_nat(val) + 1 - length(next) &*& j == special_value - idx &*&

            true == forall(xs, (sub_integer_copies)(val, 1)) &*&
            true == forall(ys, (sub_integer_copies)(val, 1)) &*&
            xs_elem == nth(i, xs) &*& ys_elem == nth(i, ys) &*&
            ys == update(i, ys_elem, xs) &*& false == mem(special_value, xs_elem) &*&
            ys_elem == append(xs_elem, cons(special_value, nil)) &*&
            0 <= i &*& i < length(xs) &*&

            (0 <= j)
                ?   next_update == update(j, nth(j, next) + 1, next)
                :   next_update == next;

        ensures
            true == forall_idx(next_update, idx, (next_from_permuts)(flatten(ys)));
    {
        switch(next_update) {
            case nil:
            case cons(n0, ns0):
                forall_idx_tail(next, idx, (next_from_permuts)(flatten(xs)));
                length_tail(next);
                length_tail(next_update);
                if (j > 0) {
                    cons_head_tail(next);
                    update_tail_tail_update(head(next), tail(next), j, nth(j, next) + 1);
                    nth_cons(j, tail(next), head(next));
                } else if (j == 0) {
                    tail_of_update_0(next, nth(j, next) + 1);
                    tail_of_update_0(next_update, nth(j, next) + 1);
                }
                next_from_permuts_update(tail(next), ns0, idx + 1, xs, ys, xs_elem, ys_elem, val, i, j - 1, special_value);
                forall_nth(xs, (sub_integer_copies)(val, 1), i);
                forall_nth(ys, (sub_integer_copies)(val, 1), i);
                assert (true == sub_integer_copies(val, 1, xs_elem));
                assert (true == sub_integer_copies(val, 1, ys_elem));
                if (mem(idx, xs_elem)) {
                    // xs_elem possesses one copy of idx
                    sub_integer_copies_val(idx, val, 1, xs_elem);
                    mem_count_bound(xs_elem, idx);
                    assert (count(xs_elem, (eq)(idx)) == 1);

                    // ys_elem possesses one copy of idx
                    sub_integer_copies_val(idx, val, 1, ys_elem);
                    mem_count_bound(ys_elem, idx);
                    assert (count(ys_elem, (eq)(idx)) == 1);

                    // Conclude on the number of occurences of idx
                    flatten_subcount_update_unrelevant(xs, ys, val, i, idx, 1);
                    forall_idx_nth(next, idx, (next_from_permuts)(flatten(xs)), 0);

                    if (j != 0) {
                        assert (true == next_from_permuts(flatten(xs), idx, nth(0, next)));
                        assert (nth(0, next) == nth(0, next_update));
                        assert (nth(0, next) == n0);
                        assert (true == next_from_permuts(flatten(xs), idx, nth(0, next_update)));
                        assert (true == next_from_permuts(flatten(ys), idx, nth(0, next_update)));
                    }

                } else if (idx == special_value) {
                    // xs_elem possesses zero copy of idx
                    mem_count_zero(xs_elem, idx);
                    assert (count(xs_elem, (eq)(idx)) == 0);

                    // ys_elem possesses one copy of n0
                    sub_integer_copies_val(idx, val, 1, ys_elem);
                    mem_count_bound(ys_elem, idx);
                    assert (count(ys_elem, (eq)(idx)) == 1);

                    // Conclude on the number of occurences of idx
                    flatten_subcount_update_relevant(xs, ys, val, i, idx);
                    forall_idx_nth(next, idx, (next_from_permuts)(flatten(xs)), 0);

                    if (j == 0) {
                        assert (true == next_from_permuts(flatten(xs), idx, nth(0, next)));
                        assert (nth(0, next) + 1 == nth(0, next_update));
                        assert (nth(0, next) + 1 == n0);
                        assert (true == next_from_permuts(flatten(xs), idx, nth(0, next)));
                        assert (true == next_from_permuts(flatten(ys), idx, nth(0, next_update)));
                    }
                } else {
                    // xs_elem possesses one copy of idx
                    mem_count_zero(xs_elem, idx);
                    assert (count(xs_elem, (eq)(idx)) == 0);

                    // ys_elem possesses one copy of idx
                    mem_count_zero(ys_elem, idx);
                    assert (count(ys_elem, (eq)(idx)) == 0);

                    // Conclude on the number of occurences of idx
                    flatten_subcount_update_unrelevant(xs, ys, val, i, idx, 0);
                    forall_idx_nth(next, idx, (next_from_permuts)(flatten(xs)), 0);

                    if (j != 0) {
                        assert (true == next_from_permuts(flatten(xs), idx, nth(0, next)));
                        assert (nth(0, next) == nth(0, next_update));
                        assert (nth(0, next) == n0);
                        assert (true == next_from_permuts(flatten(xs), idx, nth(0, next_update)));
                        assert (true == next_from_permuts(flatten(ys), idx, nth(0, next_update)));
                    }
                }
        }
    }

    lemma void count_to_mem<t>(list<t> xs, t val)
        requires    count(xs, (eq)(val)) == 0;
        ensures     false == mem(val, xs);
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0):
                count_zero_mem(xs, (eq)(val), x0);
                count_to_mem(xs0, val);
        }
    }

    lemma void mem_index<t>(list<t> xs, int i, t val)
        requires    nth(i, xs) == val &*& 0 <= i &*& i < length(xs);
        ensures     true == mem(val, xs);
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0): if (i > 0) mem_index(xs0, i - 1, val);
        }
    }

    lemma void no_dups_take_include<t>(list<t> xs, int i, t special_val)
        requires    true == no_dups(xs) &*& nth(i, xs) == special_val &*& 0 <= i &*& i < length(xs);
        ensures     count(take(i + 1, xs), (eq)(special_val)) == 1;
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0):
                if (i > 0) {
                    no_dups_take_include(xs0, i - 1, special_val);
                }
        }
    }

    lemma void no_dups_take_exclude<t>(list<t> xs, int i, t special_val)
        requires    true == no_dups(xs) &*& nth(i, xs) == special_val &*& 0 <= i &*& i < length(xs);
        ensures     count(take(i, xs), (eq)(special_val)) == 0;
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0):
                if (i == 0) {
                    take_0(xs);
                } else {
                    no_dups_take_exclude(xs0, i - 1, special_val);
                    mem_index(xs0, i - 1, special_val);
                }
        }
    }

    lemma void cht_end(list< list< pair<int,real> > > permuts, int backend_capacity)
        requires
            true == forall(permuts, (is_sub_permutation_map_fst)(backend_capacity)) &*&
            true == forall(permuts, (length_eq)(backend_capacity));
        ensures
            true == forall(permuts, is_permutation_map_fst);
    {
        switch(permuts) {
            case nil:
            case cons(p0, ps0):
                cht_end(ps0, backend_capacity);
                sub_permutation_map_fst_complete(p0);
        }
    }
@*/

int cht_fill_cht(struct Vector *cht, uint32_t cht_height, uint32_t backend_capacity)
/*@ requires
        vectorp<uint32_t>(cht, u_integer, ?old_values, ?addrs) &*&
        0 < cht_height &*& cht_height < MAX_CHT_HEIGHT &*& true == is_prime(cht_height) &*&
        0 < backend_capacity &*& backend_capacity < cht_height &*&
        sizeof(int)*MAX_CHT_HEIGHT*(backend_capacity + 1) < INT_MAX &*&
        length(old_values) == cht_height*backend_capacity &*&
        true == forall(old_values, is_one); @*/
/*@ ensures
        vectorp<uint32_t>(cht, u_integer, ?values, addrs) &*&
        (result == 0 ? true == valid_cht(values, backend_capacity, cht_height) : emp); @*/
{

    //@ mul_bounds(sizeof(int), sizeof(int), cht_height, MAX_CHT_HEIGHT);
    //@ mul_bounds(sizeof(int)*cht_height, sizeof(int)*MAX_CHT_HEIGHT, backend_capacity, backend_capacity);
    //@ mul_nonzero(sizeof(int)*cht_height, backend_capacity);

    //@ assert(0 < sizeof(int)*cht_height*backend_capacity);
    //@ assert(sizeof(int)*cht_height*backend_capacity < INT_MAX);

    // Generate the permutations of 0..(cht_height - 1) for each backend
    int *permutations = malloc(sizeof(int) * (int)(cht_height * backend_capacity));
    if (permutations == 0) {
        return 1;
    }

    for (uint32_t i = 0; i < backend_capacity; ++i)
    /*@ invariant
            0 <= i &*& i <= backend_capacity &*&
            ints(permutations, cht_height*backend_capacity, ?p) &*&
            true == forall(split(p, nat_of_int(i), cht_height), is_permutation); @*/
    {
        uint32_t offset_absolut = i * 31;
        uint64_t offset = loop(offset_absolut, cht_height);
        uint64_t base_shift = loop(i, cht_height - 1);
        uint64_t shift = base_shift + 1;
        //@ prime_is_coprime_with_anything(cht_height, shift);

        //@ open ints(permutations, cht_height*backend_capacity, ?p0_in);
        //@ close ints(permutations, cht_height*backend_capacity, p0_in);
        //@ chunk_zerosize(p0_in, i * cht_height);
        for (uint32_t j = 0; j < cht_height; ++j)
        /*@ invariant
                0 <= j &*& j <= cht_height &*&
                ints(permutations, cht_height*backend_capacity, ?p_in) &*&
                true == forall(split(p_in, nat_of_int(i), cht_height), is_permutation) &*&
                true == is_sub_permutation(chunk(p_in, i * cht_height, i * cht_height + j), cht_height) &*&
                true == forall(zip_with_index(chunk(p_in, i * cht_height, i * cht_height + j)), (is_modulo_permutation)(offset, shift, cht_height)); @*/
        {
            //@ mul_bounds(cht_height, MAX_CHT_HEIGHT, i, backend_capacity);
            //@ mul_bounds(cht_height, MAX_CHT_HEIGHT, i + 1, backend_capacity);
            //@ mul_bounds(shift, MAX_CHT_HEIGHT, j, MAX_CHT_HEIGHT);
            //@ mul_bounds(i, backend_capacity - 1, cht_height, cht_height);

            uint64_t permut = loop(offset + shift * j, cht_height);
            permutations[i * cht_height + j] = (int)permut;

            //@ pair<int,int> new_elem = pair(j, permut);
            //@ chunk_update_unrelevant(p_in, update(i * cht_height + j, permut, p_in), i * cht_height, i * cht_height + j, i * cht_height + j, permut);
            //@ split_update_unrelevant(p_in, update(i * cht_height + j, permut, p_in), nat_of_int(i), cht_height, i * cht_height + j, permut);

            //@ list<int> chunk = chunk(update(i * cht_height + j, permut, p_in), i * cht_height, i * cht_height + j);
            //@ list<int> chunk_append = append(chunk, cons(snd(new_elem), nil));
            //@ list< pair<int, int> > chunk_append_ziped = zip_with_index(chunk_append);

            //@ list< pair<int, int> > chunk_ziped = zip_with_index(chunk);
            //@ list< pair<int, int> > chunk_ziped_append = append(chunk_ziped, cons(new_elem, nil));

            // Length of chunk
            //@ chunk_length(update(i * cht_height + j, permut, p_in), i * cht_height, i * cht_height + j);
            //@ length_append(chunk, cons(snd(new_elem), nil));

            // Append rule for zip_with_index
            //@ append_to_zip(chunk, snd(new_elem));
            //@ assert (chunk_append_ziped == chunk_ziped_append);

            // Preservation of fixpoint
            //@ assert (true == forall(chunk_ziped, (is_modulo_permutation)(offset, shift, cht_height)));
            //@ assert (true == forall(cons(new_elem, nil), (is_modulo_permutation)(offset, shift, cht_height)));
            //@ forall_append(chunk_ziped, cons(new_elem, nil), (is_modulo_permutation)(offset, shift, cht_height));
            //@ assert (true == forall(chunk_ziped_append, (is_modulo_permutation)(offset, shift, cht_height)));
            //@ assert (true == forall(chunk_append_ziped, (is_modulo_permutation)(offset, shift, cht_height)));

            // Arithmetic bounds
            //@ zip_with_index_bounds(chunk_append);
            //@ lt_transitive(map(fst, chunk_append_ziped), length(chunk_append), cht_height);
            //@ modulo_permutation_bounds(chunk_append_ziped, offset, shift, cht_height);

            // No duplicates guarantee
            //@ zip_no_dups(chunk_append);
            //@ modulo_permutation_list(chunk_append_ziped, offset, shift, cht_height);

            // Prove invariant
            //@ unzip(chunk_append);
            //@ chunk_append(update(i * cht_height + j, permut, p_in), i * cht_height, i * cht_height + j);
        }

        // Conservation of invariant for for forall(split(...), ...)
        //@ open ints(permutations, cht_height*backend_capacity, ?p_in);
        //@ close ints(permutations, cht_height*backend_capacity, p_in);
        //@ list< list<int> > perms = split(p_in, nat_of_int(i), cht_height);
        //@ list< int > new_elem = chunk(p_in, i * cht_height, i * cht_height + cht_height);
        //@ mul_bounds(cht_height, cht_height, i + 1, backend_capacity);
        //@ split_append(p_in, nat_of_int(i + 1), nat_of_int(i), cht_height);
        //@ mul_nonnegative(i, cht_height);
        //@ chunk_length(p_in, i * cht_height, i * cht_height + cht_height);
        //@ sub_permutation_complete(new_elem);
        //@ forall_append(perms, cons(new_elem, nil), is_permutation);
    }

    //@ open ints(permutations, cht_height*backend_capacity, ?p_final);
    //@ close ints(permutations, cht_height*backend_capacity, p_final);
    //@ list< list<int> > perms = split(p_final, nat_of_int(backend_capacity), cht_height);

    int *next = malloc(sizeof(int) * (int)(cht_height));
    if (next == 0) {
        free(permutations);
        return 1;
    }

    //@ open ints(next, cht_height, ?n0);
    //@ close ints(next, cht_height, n0);
    for (uint32_t i = 0; i < cht_height; ++i)
    /*@ invariant
            0 <= i &*& i <= cht_height &*&
            ints(next, cht_height, ?n_init) &*&
            true == forall(take(i, n_init), (eq)(0));
    @*/
    {
        next[i] = 0;
        //@ list<int> updated_n = update(i, 0, n_init);
        //@ take_update_unrelevant(i, i, 0, n_init);
        //@ ints_to_nth(updated_n, n_init, i, 0);
        //@ append_take(updated_n, i, (eq)(0));
    }

    // End of initialization for next array
    //@ open ints(next, cht_height, ?n_init);
    //@ close ints(next, cht_height, n_init);
    //@ assert (true == forall(n_init, (eq)(0)));
    //@ bounds_from_eq(n_init, 0, backend_capacity);

    // Set up for forall(split_varlim(vals,...),...)
    //@ split_varlim_nolim(old_values, backend_capacity, n_init);
    //@ sub_permutation_map_fst_forall_nil(split_varlim(old_values, backend_capacity, n_init), backend_capacity);

    // Set up for forall(split_varlim(p_final,...),...)
    //@ gen_limits_allzero(nat_of_int(backend_capacity), 0, 0);
    //@ split_varlim_nolim(p_final, cht_height, gen_limits(nat_of_int(backend_capacity), 0, 0));
    //@ sub_permutation2_forall_nil(split_varlim(p_final, cht_height, gen_limits(nat_of_int(backend_capacity), 0, 0)), cht_height);

    // Set up for forall_idx(...)
    //@ flatten_allnil(split_varlim(p_final, cht_height, gen_limits(nat_of_int(backend_capacity), 0, 0)));
    //@ next_from_permuts_init(n_init, 0);

    // Fill the priority lists for each hash in [0, cht_height)
    for (uint32_t i = 0; i < cht_height; ++i)
    /*@invariant
        0 <= i &*& i <= cht_height &*&

        ints(permutations, cht_height*backend_capacity, p_final) &*&
        true == forall(perms, is_permutation) &*&

        ints(next, cht_height, ?n) &*&
        true == forall(n, (ge)(0)) &*&
        true == forall(n, (le)(backend_capacity)) &*&
        true == forall_idx(n, 0, (next_from_permuts)( flatten(split_varlim(p_final, cht_height, gen_limits(nat_of_int(backend_capacity), i, 0))) )) &*&

        vectorp<uint32_t>(cht, u_integer, ?vals, addrs) &*&
        length(vals) == backend_capacity * cht_height &*&
        true == forall(vals, is_one) &*&
        true == forall(split_varlim(vals, backend_capacity, n), (is_sub_permutation_map_fst)(backend_capacity))
    ; @*/
    {
        for (uint32_t j = 0; j < backend_capacity; ++j)
        /*@invariant
            0 <= j &*& j <= backend_capacity &*&

            ints(permutations, cht_height*backend_capacity, p_final) &*&
            true == forall(perms, is_permutation) &*&

            ints(next, cht_height, ?n_in) &*&
            true == forall(n_in, (ge)(0)) &*&
            true == forall(n_in, (le)(backend_capacity)) &*&
            true == forall_idx(n_in, 0, (next_from_permuts)( flatten(split_varlim(p_final, cht_height, gen_limits(nat_of_int(backend_capacity), i, j))) )) &*&

            vectorp<uint32_t>(cht, u_integer, ?vals_in, addrs) &*&
            length(vals_in) == backend_capacity * cht_height &*&
            true == forall(vals_in, is_one) &*&
            true == forall(split_varlim(vals_in, backend_capacity, n_in), (is_sub_permutation_map_fst)(backend_capacity))
        ; @*/
        {
            uint32_t *value;
            //@ mul_bounds(j, backend_capacity - 1, cht_height, cht_height);

            // Variables
            //@ list<int> limits = gen_limits(nat_of_int(backend_capacity), i, j);
            //@ list<int> limits_update = gen_limits(nat_of_int(backend_capacity), i, j+1);
            //@ list< list<int> > explored = split_varlim(p_final, cht_height, limits);
            //@ list< list<int> > explored_update = split_varlim(p_final, cht_height, limits_update);
            //@ list<int> flatten_explored = flatten(explored);
            //@ list<int> flatten_explored_update = flatten(explored_update);

            // Proof that only element explored[j] changes during the iteration
            //@ gen_limits_increment_j(nat_of_int(backend_capacity), i, j);
            //@ gen_limits_get_val(nat_of_int(backend_capacity), i, j, j);
            //@ gen_limits_get_val(nat_of_int(backend_capacity), i, j+1, j);
            //@ split_varlim_update(p_final, cht_height, limits, limits_update, j);

            // Proof that 'explored' and 'explored_append' each contains <= backend_capacity copies of 0,1,...,(cht_height-1)
            //@ split_varlim_subcount(p_final, cht_height, limits);
            //@ split_varlim_subcount(p_final, cht_height, limits_update);
            //@ flatten_subcount(explored, nat_of_int(cht_height - 1));
            //@ flatten_subcount(explored_update, nat_of_int(cht_height - 1));

            uint32_t index = j * cht_height + i;
            int bucket_id = permutations[index];

            // Proof that 0 <= bucket_id < cht_height
            //@ split_to_source(p_final, nat_of_int(backend_capacity), cht_height, i, j);
            //@ forall_nth(perms, is_permutation, j);
            //@ length_split_nth(p_final, nat_of_int(backend_capacity), cht_height, j);
            //@ forall_nth(nth(j, perms), (lt)(length(nth(j, perms))), i);
            //@ forall_nth(nth(j, perms), (ge)(0), i);
            int priority = next[bucket_id];

            // Proof that next[bucket_id] < backend_capacity
            //@ list<int> chunk_partial = chunk(p_final, j * cht_height, j * cht_height + i);
            //@ list<int> chunk_complete = chunk(p_final, j * cht_height, (j+1) * cht_height);
            //@ split_varlim_chunk_equiv(p_final, cht_height, limits, j); // chunk(p_final, j * cht_height, j * cht_height + i)
            //@ split_chunk_equiv(p_final, nat_of_int(backend_capacity), cht_height, j); // chunk(p_final, j * cht_height, (j+1) * cht_height)
            //@ forall_nth(perms, is_permutation, j);
            //@ assert(true == is_permutation(chunk_complete));
            //@ chunk_length(p_final, j * cht_height, (j+1) * cht_height);
            //@ assert(true == is_sub_permutation(chunk_complete, cht_height));
            //@ chunk_take(p_final, j * cht_height, j * cht_height + i, (j+1) * cht_height);
            //@ sub_permutation_take(chunk_complete, cht_height, i);
            //@ assert(true == is_sub_permutation(chunk_partial, cht_height));
            //@ chunk_to_source(p_final, j * cht_height, (j+1) * cht_height, i);
            //@ no_dups_take_exclude(chunk_complete, i, bucket_id);
            //@ assert( count(chunk_partial, (eq)(bucket_id)) == 0);
            //@ flatten_subcount_special(explored, nat_of_int(cht_height - 1), j, bucket_id);
            //@ forall_idx_nth(n_in, 0, (next_from_permuts)(flatten_explored), bucket_id);
            //@ assert(next[bucket_id] < backend_capacity);

            //@ forall_nth(n_in, (ge)(0), bucket_id);
            next[bucket_id] += 1;
            // Update bounds on next array
            //@ list<int> n_in_update = update(bucket_id, next[bucket_id], n_in);
            //@ forall_update(n_in, (ge)(0), bucket_id, next[bucket_id]);
            //@ forall_update(n_in, (le)(backend_capacity), bucket_id, next[bucket_id]);

            // Proof that the property on the values in n_in is preserved
            //@ list<int> chunk_partial_update = chunk(p_final, j * cht_height, j * cht_height + i+1);
            //@ split_varlim_chunk_equiv(p_final, cht_height, limits_update, j); // chunk(p_final, j * cht_height, j * cht_height + i+1)
            //@ count_to_mem(chunk_partial, bucket_id);
            //@ chunk_append(p_final, j * cht_height, j * cht_height + i);
            //@ next_from_permuts_update(n_in, n_in_update, 0, explored, explored_update, chunk_partial, chunk_partial_update, nat_of_int(cht_height-1), j, bucket_id, bucket_id);

            // Update the CHT
            //@ mul_bounds(bucket_id, cht_height - 1, backend_capacity, backend_capacity);
            //@ pair<uint32_t, real> old_val = nth(backend_capacity * bucket_id + priority, vals_in);
            vector_borrow(cht, (int)(backend_capacity * ((uint32_t)bucket_id) + ((uint32_t)priority)), (void **)&value);
            //@ forall_nth(vals_in, is_one, backend_capacity * bucket_id + priority);
            *value = j;
            vector_return(cht, (int)(backend_capacity * ((uint32_t)bucket_id) + ((uint32_t)priority)), (void *)value);
            //@ forall_update(vals_in, is_one, backend_capacity * bucket_id + priority, pair(j, 1.0));
            //@ update_update_rewrite(pair(j, 1.0), backend_capacity * bucket_id + priority, old_val, vals_in);

            // Proof that only split_varlim(vals_in,...)[bucket_id] is modified
            //@ list< pair<uint32_t, real> > vals_in_update = update(backend_capacity * bucket_id + priority, pair(j, 1.0), vals_in);
            //@ split_varlim_update_unrelevant(vals_in, vals_in_update, n_in, backend_capacity, priority, bucket_id, pair(j, 1.0));
            //@ split_varlim_update(vals_in_update, backend_capacity, n_in, n_in_update, bucket_id);

            // Proof that only element j is appended to chunk_vals
            //@ list< pair<uint32_t, real> > chunk_vals = chunk(vals_in_update, backend_capacity * bucket_id, backend_capacity * bucket_id + priority);
            //@ list< pair<uint32_t, real> > chunk_vals_update = chunk(vals_in_update, backend_capacity * bucket_id, backend_capacity * bucket_id + priority+1);
            //@ split_varlim_chunk_equiv(vals_in_update, backend_capacity, n_in, bucket_id); // chunk_vals
            //@ split_varlim_chunk_equiv(vals_in_update, backend_capacity, n_in_update, bucket_id); // chunk_vals_update
            //@ chunk_append(vals_in_update, backend_capacity * bucket_id, backend_capacity * bucket_id + priority);
            //@ assert (chunk_vals_update == append(chunk_vals, cons(pair(j, 1.0), nil)));

            // Proof that appending j preserves the permutation
            //@ list < list< pair<uint32_t, real> > > split_vals_in = split_varlim(vals_in_update, backend_capacity, n_in);
            //@ forall_nth(split_vals_in, (is_sub_permutation_map_fst)(backend_capacity), bucket_id);
            //@ assert (true == is_sub_permutation_map_fst(backend_capacity, chunk_vals));
            //@ assert (true == no_dups(map(fst, chunk_vals)));

            // goal --> false == mem(j, map(fst, chunk_vals));

            //@ assume (true == is_sub_permutation_map_fst(backend_capacity, chunk_vals_update));
            //@ forall_update(split_varlim(vals_in_update, backend_capacity, n_in), (is_sub_permutation_map_fst)(backend_capacity), bucket_id, chunk_vals_update);
        }

        // Conservation of invariant for for forall_idx(...)
        //@ open ints(next, cht_height, ?n_in);
        //@ close ints(next, cht_height, n_in);
        //@ assert(true == forall_idx(n_in, 0, (next_from_permuts)( flatten(split_varlim(p_final, cht_height, gen_limits(nat_of_int(backend_capacity), i, backend_capacity))) )));
        //@ gen_limits_increment_i(nat_of_int(backend_capacity), i);
    }

    //@ open ints(next, cht_height, ?n);
    //@ close ints(next, cht_height, n);
    //@ assert vectorp<uint32_t>(cht, u_integer, ?vals, addrs);

    // Proof that next == [backend_capacity, backend_capacity, ..., backend_capacity]
    //@ list<int> all_p_final = flatten(split(p_final, nat_of_int(backend_capacity), cht_height));
    //@ gen_limits_all_same(nat_of_int(backend_capacity), cht_height);
    //@ split_varlim_split_equiv(p_final, gen_limits(nat_of_int(backend_capacity), cht_height, 0), cht_height, nat_of_int(backend_capacity));
    //@ permutation_list_to_count(p_final, nat_of_int(backend_capacity), cht_height);
    //@ flatten_count(split(p_final, nat_of_int(backend_capacity), cht_height), nat_of_int(cht_height - 1));
    //@ assert (true == integer_copies(nat_of_int(cht_height - 1), backend_capacity, all_p_final));
    //@ assert (true == forall_idx(n, 0, (next_from_permuts)(all_p_final)));
    //@ next_from_permuts_end(n, 0, nat_of_int(cht_height - 1), backend_capacity, all_p_final);

    // Proof that the CHT is completely filled with permutations
    //@ list< list< pair<uint32_t, real> > > permuts = split(vals, nat_of_int(cht_height), backend_capacity);
    //@ split_varlim_split_equiv(vals, n, backend_capacity, nat_of_int(cht_height));
    //@ mul_bounds(backend_capacity, backend_capacity, 1, cht_height);
    //@ length_split_forall(vals, nat_of_int(cht_height), backend_capacity);
    //@ cht_end(permuts, backend_capacity);
    //@ assert (true == valid_cht(vals, backend_capacity, cht_height));

    // Free memory
    free(next);
    free(permutations);
    return 0;
}

/*@

    lemma void exists_index<t>(list<t> xs, fixpoint(t,bool) f, int i)
        requires    0 <= i &*& i < length(xs) &*& true == f(nth(i, xs));
        ensures     true == exists(xs, f);
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0): if (i > 0) exists_index(xs0, f, i - 1);
        }
    }

    lemma void exists_none<t>(list<t> xs, fixpoint(t,bool) f)
        requires    true == forall( xs, (sup)( (eq)(false), f) );
        ensures     false == exists(xs, f);
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0): exists_none(xs0, f);
        }
    }

    lemma void cht_exists_from_dchain(int hash, list<pair<int, real> > cht, dchain filter, int i, int cht_height, int backend_capacity)
        requires
            true == dchain_allocated_fp(filter, nth((hash%cht_height) * backend_capacity + i, map(fst, cht))) &*&
            0 <= i &*& i < dchain_index_range_fp(filter) &*&
            length(cht) == backend_capacity * cht_height &*&
            dchain_index_range_fp(filter) == backend_capacity &*&
            0 < cht_height &*& 0 < backend_capacity &*& 0 <= hash;
        ensures
            true == cht_exists(hash, cht, filter);
    {
        int start = hash%cht_height;
        list<int> chunk = chunk(map(fst, cht), start * backend_capacity, (start + 1) * backend_capacity);

        div_mod_gt_0(start, hash, cht_height);
        assume (length(cht)/dchain_index_range_fp(filter) == cht_height);
        mul_nonnegative(start, backend_capacity);
        mul_bounds(start + 1, cht_height, backend_capacity, backend_capacity);
        map_preserves_length(fst, cht);
        chunk_to_source(map(fst, cht), start * backend_capacity, (start + 1) * backend_capacity, i);
        chunk_length(map(fst, cht), start * backend_capacity, (start + 1) * backend_capacity);
        exists_index(chunk, (dchain_allocated_fp)(filter), i);
    }

    lemma void cht_exists_neg(int hash, list<pair<int, real> > cht, dchain filter, int cht_height, int backend_capacity)
        requires
            true == forall(chunk(map(fst, cht), (hash%cht_height) * backend_capacity,  ((hash%cht_height) + 1) * backend_capacity), (sup)( (eq)(false), (dchain_allocated_fp)(filter))) &*&
            length(cht) == backend_capacity * cht_height &*&
            dchain_index_range_fp(filter) == backend_capacity &*&
            0 < cht_height &*& 0 < backend_capacity &*& 0 <= hash;
        ensures
            false == cht_exists(hash, cht, filter);
    {
        int start = hash%cht_height;
        list<int> chunk = chunk(map(fst, cht), start * backend_capacity, (start + 1) * backend_capacity);

        div_mod_gt_0(start, hash, cht_height);
        assume (length(cht)/dchain_index_range_fp(filter) == cht_height);
        mul_nonnegative(start, backend_capacity);
        mul_bounds(start + 1, cht_height, backend_capacity, backend_capacity);
        map_preserves_length(fst, cht);
        exists_none(chunk, (dchain_allocated_fp)(filter));
    }

    lemma void cht_choose_index(int hash, list<pair<int, real> > cht, dchain filter, int i, int cht_height, int backend_capacity)
        requires
            true == forall(take(i, chunk(map(fst, cht), (hash%cht_height) * backend_capacity,  ((hash%cht_height) + 1) * backend_capacity)), (sup)( (eq)(false), (dchain_allocated_fp)(filter))) &*&
            true == dchain_allocated_fp(filter, nth((hash%cht_height) * backend_capacity + i, map(fst, cht))) &*&
            length(cht) == backend_capacity * cht_height &*&
            dchain_index_range_fp(filter) == backend_capacity &*&
            0 < cht_height &*& 0 < backend_capacity &*& 0 <= hash;
        ensures
            cht_choose(hash, cht, filter) == nth((hash%cht_height) * backend_capacity + i, map(fst, cht));
    {
        int start = hash%cht_height;
        list<int> chunk = chunk(map(fst, cht), start * backend_capacity, (start + 1) * backend_capacity);

        div_mod_gt_0(start, hash, cht_height);
        assume (length(cht)/dchain_index_range_fp(filter) == cht_height);
        mul_nonnegative(start, backend_capacity);
        mul_bounds(start + 1, cht_height, backend_capacity, backend_capacity);
        map_preserves_length(fst, cht);
        chunk_to_source(map(fst, cht), start * backend_capacity, (start + 1) * backend_capacity, i);
        index_of_fp_exists(chunk, 0, (dchain_allocated_fp)(filter), i);
    }

@*/

int cht_find_preferred_available_backend(uint64_t hash, struct Vector *cht, struct DoubleChain *active_backends, uint32_t cht_height, uint32_t backend_capacity, int *chosen_backend)
/*@ requires
        vectorp<uint32_t>(cht, u_integer, ?values, ?addrs) &*&
        double_chainp(?ch, active_backends) &*&
        *chosen_backend |-> _ &*&
        dchain_index_range_fp(ch) == backend_capacity &*&
        true == valid_cht(values, backend_capacity, cht_height); @*/
/*@ ensures
        vectorp<uint32_t>(cht, u_integer, values, addrs) &*&
        double_chainp(ch, active_backends) &*&
        *chosen_backend |-> ?chosen &*&
        (result == 0
            ? false == cht_exists(hash, values, ch)
            : true == cht_exists(hash, values, ch) &*&
            chosen == cht_choose(hash, values, ch) &*&
            result == 1 &*&
            0 <= chosen &*& chosen < dchain_index_range_fp(ch)
        ); @*/
{
    uint64_t start = loop(hash, cht_height);
    for (uint32_t i = 0; i < backend_capacity; ++i)
    /*@invariant
        0 <= i &*& i <= backend_capacity &*&
        0 <= start &*& start < cht_height &*&

        vectorp<uint32_t>(cht, u_integer, values, addrs) &*&
        cht_height*backend_capacity == length(values) &*&
        true == forall(values, is_one) &*&

        double_chainp(ch, active_backends) &*&
        *chosen_backend |-> _ &*&

        true == forall(chunk(map(fst, values), start * backend_capacity, start * backend_capacity + i), (sup)( (eq)(false), (dchain_allocated_fp)(ch)))
    ;@*/
    {
        //@ mul_bounds(start, cht_height, backend_capacity, backend_capacity);
        //@ mul_bounds(start+1, cht_height, backend_capacity, backend_capacity);
        //@ mul_bounds(cht_height, MAX_CHT_HEIGHT, backend_capacity, backend_capacity);
        uint64_t candidate_idx = start * backend_capacity + i; // There was a bug, right here, untill I tried to prove this.

        uint32_t *candidate;
        vector_borrow(cht, (int)candidate_idx, (void **)&candidate);

        //@ list< list< pair<uint32_t,real> > > permuts = split(values, nat_of_int(cht_height), backend_capacity);
        //@ list< pair<uint32_t,real> > candidate_chunk = chunk(values, start * backend_capacity, (start+1) * backend_capacity);

        // Proof that 0 <= map(fst, values)[candiadate_idx] < backend_capacity
        //@ length_split(values, nat_of_int(cht_height), backend_capacity);
        //@ forall_nth(permuts, is_permutation_map_fst, start);
        //@ split_chunk_equiv(values, nat_of_int(cht_height), backend_capacity, start);
        //@ assert (true == is_permutation_map_fst(candidate_chunk));
        //@ is_permutation_map_fst_extract(candidate_chunk, map(fst, candidate_chunk));
        //@ map_preserves_length(fst, candidate_chunk);
        //@ chunk_length(values, start * backend_capacity, (start+1) * backend_capacity);
        //@ forall_nth(map(fst, candidate_chunk), (ge)(0), i);
        //@ forall_nth(map(fst, candidate_chunk), (lt)(backend_capacity), i);
        //@ chunk_to_source(values, start * backend_capacity, (start+1) * backend_capacity, i);
        //@ nth_map(i, fst, candidate_chunk);
        //@ assert (fst(nth(candidate_idx, values)) < backend_capacity);
        //@ nth_map(candidate_idx, fst, values);
        //@ assert (nth(candidate_idx, map(fst, values)) < backend_capacity);
        //@ assert (0 <= nth(candidate_idx, map(fst, values)));

        ////@ update_id(candidate_idx, values);
        //@ forall_nth(values, is_one, candidate_idx);
        if (dchain_is_index_allocated(active_backends, (int)*candidate)) {
            *chosen_backend = (int)*candidate;

            // Proof for cht_exists
            //@ assert (true == dchain_allocated_fp(ch, *candidate));
            //@ assert (nth(candidate_idx, map(fst, values)) == *candidate);
            //@ cht_exists_from_dchain(hash, values, ch, i, cht_height, backend_capacity);

            // Proof for cht_choose
            //@ assert candidate |-> ?chosen_candidate;
            //@ mul_bounds(start + 1, cht_height, backend_capacity, backend_capacity);
            //@ map_preserves_length(fst, values);
            //@ chunk_length(map(fst, values), start * backend_capacity, (start + 1) * backend_capacity);
            //@ chunk_take(map(fst, values), start * backend_capacity, start * backend_capacity + i, (start + 1) * backend_capacity);
            //@ cht_choose_index(hash, values, ch, i, cht_height, backend_capacity);
            //@ assert(fst(nth(candidate_idx, values)) == cht_choose(hash, values, ch));

            vector_return(cht, (int)candidate_idx, candidate);
            return 1;
        }

        // Conservation of forall(chunk(...), ...);
        //@ assert (false == dchain_allocated_fp(ch, *candidate));
        //@ map_preserves_length(fst, values);
        //@ chunk_append(map(fst, values), start * backend_capacity, start * backend_capacity + i);
        //@ forall_append(chunk(map(fst, values), start * backend_capacity, start * backend_capacity + i), cons(nth(candidate_idx, map(fst, values)), nil),  (sup)( (eq)(false), (dchain_allocated_fp)(ch)));
        vector_return(cht, (int)candidate_idx, candidate);
    }
    //@ cht_exists_neg(hash, values, ch, cht_height, backend_capacity);
    //@ assert(false == cht_exists(hash, values, ch));
    return 0;
}
