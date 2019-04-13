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

    lemma void bounds_from_eq(list<int> xs, int x, int up_bound)
        requires    true == forall(xs, (eq)(x)) &*& x <= up_bound;
        ensures     true == forall(xs, (le)(up_bound)) &*& true == forall(xs, (ge)(x));
    {
        switch(xs){
            case nil:
            case cons(x0, xs0): bounds_from_eq(xs0, x, up_bound);
        }
    }

    lemma void forall2_eq_cst<t>(list<t> l1, list<t> l2, t val)
        requires    true == forall(l1, (eq)(val)) &*& true == forall(l2, (eq)(val));
        ensures     true == forall2(l1, l2, eq);
    {
        switch(l1) {
            case nil:
            case cons(h1, t1):
                switch(l2) {
                    case nil:
                    case cons(h2, t2): 
                        forall_nth(l1, (eq)(val), 0);
                        forall_nth(l2, (eq)(val), 0);
                        forall2_eq_cst(t1, t2, val);
                }
        }
    }

    lemma void map_preserves_update<t1,t2>(list<t1> xs, list<t1> xs_update, fixpoint (t1,t2) fp, int i, t1 val)
        requires    xs_update == update(i, val, xs) &*& 0 <= i &*& i < length(xs);
        ensures     map(fp, xs_update) == update(i, fp(val), map(fp, xs));
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0): {
                switch(xs_update) {
                    case nil:
                    case cons(x0_update, xs0_update): if (i > 0) map_preserves_update(xs0, xs0_update, fp, i - 1, val);
                }
            }
        }
    }

    // ------------- 2nd double-nested loop -------------

    fixpoint list<int> filter_transpose(list<int> p_transpose, int limit, int bucket_id) {
        return filter_idx(take(limit, p_transpose), 0, (eq)(bucket_id));
    }

    fixpoint list<int> next_invariant(list<int> p_transpose, int limit, int cht_height, nat idx) {
        switch(idx) {
            case zero: return nil;
            case succ(idx_pred): return cons( length(filter_transpose(p_transpose, limit, cht_height - int_of_nat(idx))) , next_invariant(p_transpose, limit, cht_height, idx_pred) );
        }
    }

    lemma_auto(length(next_invariant(p_transpose, limit, cht_height, idx))) void length_next_invariant(list<int> p_transpose, int limit, int cht_height, nat idx)
        requires    true;
        ensures     length(next_invariant(p_transpose, limit, cht_height, idx)) == int_of_nat(idx);
    {
        switch(idx) {
            case zero:
            case succ(idx_pred): length_next_invariant(p_transpose, limit, cht_height, idx_pred);
        }
    }

    lemma void next_invariant_init(list<int> p_transpose, int cht_height, nat idx)
        requires    true;
        ensures     true == forall(next_invariant(p_transpose, 0, cht_height, idx), (eq)(0));
    {
        switch(idx) {
            case zero:
            case succ(idx_pred):
                assert (take(0, p_transpose) == nil);
                assert(count(nil, (eq)(cht_height - int_of_nat(idx))) == 0);
                filter_idx_count_to_length(take(0, p_transpose), 0,  (eq)(cht_height - int_of_nat(idx)), 0);
                next_invariant_init(p_transpose, cht_height, idx_pred);
        }
    }

    lemma void next_invariant_val(list<int> p_transpose, int limit, int cht_height, nat idx, int i)
        requires    0 <= i &*& i < int_of_nat(idx) &*& int_of_nat(idx) <= cht_height;
        ensures     nth(i, next_invariant(p_transpose, limit, cht_height, idx)) == length(filter_transpose(p_transpose, limit, i + (cht_height - int_of_nat(idx))));
    {
        switch(idx) {
            case zero:
            case succ(idx_pred): if (i > 0) next_invariant_val(p_transpose, limit, cht_height, idx_pred, i - 1);
        }
    }

    lemma void next_invariant_update(list<int> p_transpose, int limit, int cht_height, nat idx, int bucket_id)
        requires    
            nth(limit, p_transpose) == bucket_id &*& 
            0 <= bucket_id &*& bucket_id < cht_height &*&
            0 <= limit &*& limit < length(p_transpose) &*&
            int_of_nat(idx) <= cht_height; 
        ensures
            (cht_height - int_of_nat(idx) <= bucket_id)
                ?   next_invariant(p_transpose, limit + 1, cht_height, idx) == 
                    update(bucket_id - (cht_height - int_of_nat(idx)), nth(bucket_id - (cht_height - int_of_nat(idx)), next_invariant(p_transpose, limit, cht_height, idx)) + 1, next_invariant(p_transpose, limit, cht_height, idx))
                :   next_invariant(p_transpose, limit + 1, cht_height, idx) == next_invariant(p_transpose, limit, cht_height, idx);
    {
        switch(idx) {
            case zero:
            case succ(idx_pred):
                // Variables
                int diff = cht_height - int_of_nat(idx);
                list<int> lim_p_transpose = take(limit, p_transpose);
                list<int> cur_list = filter_transpose(p_transpose, limit, diff);
                list<int> new_elem = cons(nth(limit, p_transpose), nil);
                
                // Prove the property for the head
                take_plus_one(limit, p_transpose);
                filter_idx_length_to_count(lim_p_transpose, 0, (eq)(diff), length(cur_list));
                if (bucket_id == diff) {
                    filter_idx_count_append(lim_p_transpose, new_elem, 0, (eq)(diff), length(cur_list), 1);
                } else{
                    filter_idx_count_append(lim_p_transpose, new_elem, 0, (eq)(diff), length(cur_list), 0);
                } 

                // Recursive call
                next_invariant_update(p_transpose, limit, cht_height, idx_pred, bucket_id);
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

    fixpoint list< list<int> > cht_invariant(list<int> p_transpose, int limit, int backend_capacity, int cht_height, nat idx) {
        switch(idx) {
            case zero: return nil;
            case succ(idx_pred): return cons( map((extract_column)(backend_capacity), filter_transpose(p_transpose, limit, cht_height - int_of_nat(idx))), cht_invariant(p_transpose, limit, backend_capacity, cht_height, idx_pred));
        }
    }

    lemma_auto(length(cht_invariant(p_transpose, limit, backend_capacity, cht_height, idx))) void length_cht_invariant(list<int> p_transpose, int limit, int backend_capacity, int cht_height, nat idx)
        requires    true;
        ensures     length(cht_invariant(p_transpose, limit, backend_capacity, cht_height, idx)) == int_of_nat(idx);
    {
        switch(idx) {
            case zero:
            case succ(idx_pred): length_cht_invariant(p_transpose, limit, backend_capacity, cht_height, idx_pred);
        }
    }

    lemma void cht_invariant_init(list<int> p_transpose, int backend_capacity, int cht_height, nat idx)
        requires    true;
        ensures     true == forall(cht_invariant(p_transpose, 0, backend_capacity, cht_height, idx), (eq)(nil));
    {
        switch(idx) {
            case zero:
            case succ(idx_pred):
                assert (take(0, p_transpose) == nil);
                assert(count(nil, (eq)(cht_height - int_of_nat(idx))) == 0);
                filter_idx_count_to_length(take(0, p_transpose), 0, (eq)(cht_height - int_of_nat(idx)), 0);
                map_preserves_length((extract_column)(cht_height), filter_transpose(p_transpose, 0, cht_height - int_of_nat(idx)));
                cht_invariant_init(p_transpose, backend_capacity, cht_height, idx_pred);
        }
    }

    lemma void cht_invariant_val(list<int> p_transpose, int limit, int backend_capacity, int cht_height, nat idx, int i)
        requires    0 <= i &*& i < int_of_nat(idx) &*& int_of_nat(idx) <= cht_height;
        ensures     nth(i, cht_invariant(p_transpose, limit, backend_capacity, cht_height, idx)) == map((extract_column)(backend_capacity), filter_transpose(p_transpose, limit, i + (cht_height - int_of_nat(idx))));
    {
        switch(idx) {
            case zero:
            case succ(idx_pred): if (i > 0) cht_invariant_val(p_transpose, limit, backend_capacity, cht_height, idx_pred, i - 1);
        }
    }

    lemma void cht_invariant_update(list<int> p_transpose, int limit, int backend_capacity, int cht_height, nat idx, int bucket_id, int i, int j)
        requires    
            nth(limit, p_transpose) == bucket_id &*& limit == i * backend_capacity + j &*& 
            0 <= i &*& 0 <= j &*& 0 < backend_capacity &*&
            0 <= bucket_id &*& bucket_id < cht_height &*&
            0 <= limit &*& limit < length(p_transpose) &*&
            int_of_nat(idx) <= cht_height; 
        ensures
            (cht_height - int_of_nat(idx) <= bucket_id)
                ?   cht_invariant(p_transpose, limit + 1, backend_capacity, cht_height, idx) == 
                    update(bucket_id - (cht_height - int_of_nat(idx)), append(nth(bucket_id - (cht_height - int_of_nat(idx)), cht_invariant(p_transpose, limit, backend_capacity, cht_height, idx)), cons(j, nil)), cht_invariant(p_transpose, limit, backend_capacity, cht_height, idx))
                :   cht_invariant(p_transpose, limit + 1, backend_capacity, cht_height, idx) == cht_invariant(p_transpose, limit, backend_capacity, cht_height, idx);
    {
        switch(idx) {
            case zero:
            case succ(idx_pred):
                // Variables
                int diff = cht_height - int_of_nat(idx);
                list<int> lim_p_transpose = take(limit, p_transpose);
                list<int> cur_list = filter_transpose(p_transpose, limit, diff);
                int new_elem = nth(limit, p_transpose);
                
                // Prove the property for the head
                take_plus_one(limit, p_transpose);
                filter_idx_length_to_count(lim_p_transpose, 0, (eq)(diff), length(cur_list));
                if (bucket_id == diff) {
                    take_plus_one(limit, p_transpose);
                    filter_idx_include_last(lim_p_transpose, 0, (eq)(diff), new_elem);
                    map_append((extract_column)(backend_capacity), filter_transpose(p_transpose, limit, cht_height - int_of_nat(idx)), cons(limit, nil));
                    extract_column_val(backend_capacity, limit, i, j);
                } else{
                    filter_idx_drop_last(lim_p_transpose, 0, (eq)(diff), new_elem);
                } 

                // Recursive call
                cht_invariant_update(p_transpose, limit, backend_capacity, cht_height, idx_pred, bucket_id, i, j);
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

    //@ open ints(permutations, cht_height*backend_capacity, ?p_final);
    //@ close ints(permutations, cht_height*backend_capacity, p_final);

    // Useful variables for later
    //@ list< list<int> > perms = split(p_final, nat_of_int(backend_capacity), cht_height);
    //@ list<int> p_transpose = transpose(p_final, backend_capacity, cht_height);

    // Set up for invariant on next
    //@ next_invariant_init(p_transpose, cht_height, nat_of_int(cht_height));
    //@ forall2_eq_cst(n_init, next_invariant(p_transpose, 0, cht_height, nat_of_int(cht_height)), 0);

    // Set up for invariant on cht
    //@ map_preserves_length(fst, old_values);
    //@ split_varlim_nolim(map(fst, old_values), backend_capacity, n_init);
    //@ cht_invariant_init(p_transpose, backend_capacity, cht_height, nat_of_int(cht_height));
    //@ forall2_eq_cst(split_varlim(map(fst, old_values), backend_capacity, n_init), cht_invariant(p_transpose, 0, backend_capacity, cht_height, nat_of_int(cht_height)), nil);

    // Fill the priority lists for each hash in [0, cht_height)
    for (uint32_t i = 0; i < cht_height; ++i)
    /*@invariant
        0 <= i &*& i <= cht_height &*&

        ints(permutations, cht_height*backend_capacity, p_final) &*&
        true == forall(perms, is_permutation) &*&

        ints(next, cht_height, ?n) &*&
        true == forall(n, (ge)(0)) &*&
        true == forall(n, (le)(backend_capacity)) &*&
        true == forall2(n, next_invariant(p_transpose, i * backend_capacity, cht_height, nat_of_int(cht_height)), eq) &*& // invariant on next

        vectorp<uint32_t>(cht, u_integer, ?vals, addrs) &*&
        length(vals) == backend_capacity * cht_height &*&
        true == forall(vals, is_one) &*&
        true == forall2(split_varlim(map(fst, vals), backend_capacity, n), cht_invariant(p_transpose, i * backend_capacity, backend_capacity, cht_height, nat_of_int(cht_height)), eq) // invariant on cht
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
            true == forall2(n_in, next_invariant(p_transpose, i * backend_capacity + j, cht_height, nat_of_int(cht_height)), eq) &*& // invariant on next

            vectorp<uint32_t>(cht, u_integer, ?vals_in, addrs) &*&
            length(vals_in) == backend_capacity * cht_height &*&
            true == forall(vals_in, is_one) &*&
            true == forall2(split_varlim(map(fst, vals_in), backend_capacity, n_in), cht_invariant(p_transpose, i * backend_capacity + j, backend_capacity, cht_height, nat_of_int(cht_height)), eq) // invariant on cht
        ; @*/
        {
            uint32_t *value;

            //@ mul_bounds(j, backend_capacity - 1, cht_height, cht_height);
            uint32_t index = j * cht_height + i;
            int bucket_id = permutations[index];

            // Proof that 0 <= bucket_id < cht_height
            //@ split_to_source(p_final, nat_of_int(backend_capacity), cht_height, i, j);
            //@ forall_nth(perms, is_permutation, j);
            //@ length_split_nth(p_final, nat_of_int(backend_capacity), cht_height, j);
            //@ forall_nth(nth(j, perms), (lt)(length(nth(j, perms))), i);
            //@ forall_nth(nth(j, perms), (ge)(0), i);
            int priority = next[bucket_id];

            // Variables
            //@ int limit = i * backend_capacity + j;
            //@ int limit_update = i * backend_capacity + (j+1);
            //@ list<int> next_invar = next_invariant(p_transpose, limit, cht_height, nat_of_int(cht_height));
            //@ list<int> next_invar_update = next_invariant(p_transpose, limit_update, cht_height, nat_of_int(cht_height));
            //@ list<int> filter_bucket = filter_transpose(p_transpose, limit, bucket_id);
            //@ list<int> filter_bucket_update = filter_transpose(p_transpose, limit_update, bucket_id);

            // Proof that next_invar_update = update(bucket_id, next_invar[bucket_id] + 1, next_invar)
            //@ transpose_to_src(p_final, p_transpose, backend_capacity, cht_height, j, i);
            //@ mul_nonnegative(i, backend_capacity);
            //@ mul_bounds(i, cht_height - 1, backend_capacity, backend_capacity);
            //@ next_invariant_update(p_transpose, i * backend_capacity + j, cht_height, nat_of_int(cht_height), bucket_id);

            //@ next_invariant_val(p_transpose, limit, cht_height, nat_of_int(cht_height), bucket_id);
            //@ next_invariant_val(p_transpose, limit_update, cht_height, nat_of_int(cht_height), bucket_id);
            //@ assert (length(filter_bucket_update) == length(filter_bucket) + 1);

            // Proof that next[bucket_id] == next_invar[bucket_id] == length(filter_bucket) < backend_capacity
            //@ list<int> take_limit_update = take(limit_update, p_transpose);
            //@ list<int> drop_limit_update = drop(limit_update, p_transpose);
            //@ permutation_split_to_count(p_final, nat_of_int(backend_capacity), cht_height);
            //@ integer_copies_val(bucket_id, nat_of_int(cht_height - 1), backend_capacity, p_final);
            //@ transpose_preserves_count(p_final, backend_capacity, cht_height, backend_capacity, (eq)(bucket_id));
            //@ assert (p_transpose == append(take_limit_update, drop_limit_update));
            //@ filter_idx_length_to_count(take_limit_update, 0, (eq)(bucket_id), length(filter_bucket_update));
            //@ count_nonnegative(drop_limit_update, (eq)(bucket_id));
            //@ count_append(take_limit_update, drop_limit_update, (eq)(bucket_id));
            //@ assert (length(filter_bucket) < backend_capacity);
            //@ forall2_nth(n_in, next_invar, eq, bucket_id);
            //@ assert(next[bucket_id] < backend_capacity);

            //@ forall_nth(n_in, (ge)(0), bucket_id);
            next[bucket_id] += 1;

            // Prove that the invariant on next is preserved 
            //@ list<int> n_in_update = update(bucket_id, next[bucket_id], n_in);
            //@ forall_update(n_in, (ge)(0), bucket_id, next[bucket_id]);
            //@ forall_update(n_in, (le)(backend_capacity), bucket_id, next[bucket_id]);
            //@ assert(nth(bucket_id, n_in) == nth(bucket_id, next_invar));
            //@ assert(nth(bucket_id, n_in_update) == nth(bucket_id, next_invar_update));
            //@ forall2_update(n_in, next_invar, eq, bucket_id, nth(bucket_id, n_in_update), nth(bucket_id, next_invar_update));

            // -----------------------------------

            // Update the CHT
            //@ mul_bounds(bucket_id, cht_height - 1, backend_capacity, backend_capacity);
            //@ pair<uint32_t, real> old_val = nth(backend_capacity * bucket_id + priority, vals_in);
            vector_borrow(cht, (int)(backend_capacity * ((uint32_t)bucket_id) + ((uint32_t)priority)), (void **)&value);
            //@ forall_nth(vals_in, is_one, backend_capacity * bucket_id + priority);
            *value = j;
            vector_return(cht, (int)(backend_capacity * ((uint32_t)bucket_id) + ((uint32_t)priority)), (void *)value);
            //@ forall_update(vals_in, is_one, backend_capacity * bucket_id + priority, pair(j, 1.0));
            //@ update_update_rewrite(pair(j, 1.0), backend_capacity * bucket_id + priority, old_val, vals_in);
            
            // Variables
            //@ list< pair<uint32_t, real> > vals_in_update = update(backend_capacity * bucket_id + priority, pair(j, 1.0), vals_in);
            //@ list<uint32_t> map_vals_in = map(fst, vals_in);
            //@ list<uint32_t> map_vals_in_update = map(fst, vals_in_update);
            //@ list< list<int> > cht_split = split_varlim(map_vals_in, backend_capacity, n_in);
            //@ list< list<int> > cht_split_update = split_varlim(map_vals_in_update, backend_capacity, n_in_update);
            //@ list< list<int> > cht_invar = cht_invariant(p_transpose, limit, backend_capacity, cht_height, nat_of_int(cht_height));
            //@ list< list<int> > cht_invar_update =  cht_invariant(p_transpose, limit_update, backend_capacity, cht_height, nat_of_int(cht_height));

            // Proof that only cht_split[bucket_id] is modified
            //@ map_preserves_update(vals_in, vals_in_update, fst, backend_capacity * bucket_id + priority, pair(j, 1.0));
            //@ nth_map(backend_capacity * bucket_id + priority, fst, vals_in_update);
            //@ map_preserves_length(fst, vals_in);
            //@ split_varlim_update_unrelevant(map_vals_in, map_vals_in_update, n_in, backend_capacity, priority, bucket_id, j);
            //@ split_varlim_update(map_vals_in_update, backend_capacity, n_in, n_in_update, bucket_id);

            // Proof that cht_split_update[bucket_id] = append(cht_split[bucket_id], cons(j, nil));
            //@ list<uint32_t> chunk_vals = chunk(map_vals_in_update, backend_capacity * bucket_id, backend_capacity * bucket_id + priority);
            //@ list<uint32_t> chunk_vals_update = chunk(map_vals_in_update, backend_capacity * bucket_id, backend_capacity * bucket_id + priority+1);
            //@ split_varlim_chunk_equiv(map_vals_in_update, backend_capacity, n_in, bucket_id); // chunk_vals
            //@ split_varlim_chunk_equiv(map_vals_in_update, backend_capacity, n_in_update, bucket_id); // chunk_vals_update
            //@ chunk_append(map_vals_in_update, backend_capacity * bucket_id, backend_capacity * bucket_id + priority);
            //@ assert (chunk_vals_update == append(chunk_vals, cons(j, nil)));

            // Proof that cht_invar_update == update(bucket_id, append(cht_invar[bucket_id], cons(j, nil)), cht_invar)
            //@ list<uint32_t> indexes = map((extract_column)(backend_capacity), filter_bucket);
            //@ list<uint32_t> indexes_update = map((extract_column)(backend_capacity), filter_bucket_update);
            //@ cht_invariant_update(p_transpose, limit, backend_capacity, cht_height, nat_of_int(cht_height), bucket_id, i, j);
            //@ cht_invariant_val(p_transpose, limit, backend_capacity, cht_height, nat_of_int(cht_height), bucket_id);
            //@ cht_invariant_val(p_transpose, limit_update, backend_capacity, cht_height, nat_of_int(cht_height), bucket_id);
            //@ assert (indexes_update == append(indexes, cons(j, nil)));
           
            // Prove that the invariant on cht is preserved 
            //@ forall2_nth(cht_split, cht_invar, eq, bucket_id);
            //@ assert(chunk_vals_update == indexes_update);
            //@ forall2_update(cht_split, cht_invar, eq, bucket_id, nth(bucket_id, cht_split_update), nth(bucket_id, cht_invar_update));
        }
    }
    //@ assert vectorp<uint32_t>(cht, u_integer, ?vals, addrs);

    // Proof that the CHT is completely filled with permutations
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
