#include "cht.h"
#include <assert.h>
#include <stdlib.h>

//@ #include "prime.gh"
//@ #include "permutlist.gh"

static uint64_t loop(uint64_t k, uint64_t capacity)
//@ requires 0 < capacity &*& capacity < INT_MAX;
/*@ ensures 0 <= result &*& result < capacity &*& result == k%capacity; @*/
{
    uint64_t g = k % capacity;
    //@ div_mod_gt_0(g, k, capacity);
    return g;
}

/*@
    fixpoint bool is_modulo_permutation(int offset, int shift, int cht_height, pair<int, int> index_elem_pair) {
        return snd(index_elem_pair) == ((offset + shift * fst(index_elem_pair)) % cht_height);
    }

    lemma void mul_nonzero(int a, int b)
        requires a > 0 &*& b > 0;
        ensures a * b > 0;
    {
        mul_nonnegative(a - 1, b);
        assert (a-1)*b < a*b;
    }

    fixpoint bool gt(int x, int y) { return x < y; }

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
            case cons(x0, xs0):
                lt_transitive(xs0, bound, up_bound);
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

    fixpoint bool is_cst<t>(t ref, t x) {
        return ref == x;
    }

@*/

void cht_fill_cht(struct Vector *cht, uint32_t cht_height, uint32_t backend_capacity)
/*@ requires vectorp<uint32_t>(cht, u_integer, ?old_values, ?addrs) &*&
             0 < cht_height &*& cht_height < MAX_CHT_HEIGHT &*& true == is_prime(cht_height) &*&
             0 < backend_capacity &*& backend_capacity < cht_height &*&
             sizeof(int)*MAX_CHT_HEIGHT*backend_capacity < INT_MAX &*&
             length(old_values) == cht_height*backend_capacity &*&
             true == forall(old_values, is_one); @*/
/*@ ensures vectorp<uint32_t>(cht, u_integer, ?values, addrs) &*&
            true == valid_cht(values, backend_capacity, cht_height); @*/
{

    //@ mul_bounds(sizeof(int), sizeof(int), cht_height, MAX_CHT_HEIGHT);
    //@ mul_bounds(sizeof(int)*cht_height, sizeof(int)*MAX_CHT_HEIGHT, backend_capacity, backend_capacity);
    //@ mul_nonzero(sizeof(int)*cht_height, backend_capacity);

    //@ assert(0 < sizeof(int)*cht_height*backend_capacity);
    //@ assert(sizeof(int)*cht_height*backend_capacity < INT_MAX);

    // Generate the permutations of 0..(cht_height - 1) for each backend
    int *permutations = malloc(sizeof(int) * (int)(cht_height * backend_capacity));
    //@ assume(permutations != 0);//TODO: report failure

    //// @ open ints(permutations, cht_height*backend_capacity, ?p0);
    //// @ close ints(permutations, cht_height*backend_capacity, p0);
    //// @ close foreach(list_split_every_n(p0, zero, cht_height), permutation);
    for (uint32_t i = 0; i < backend_capacity; ++i)
    /*@ invariant 
            0 <= i &*& i <= backend_capacity &*&
            ints(permutations, cht_height*backend_capacity, ?p);@*/
            //forall(list_split_every_n(p, nat_of_int(i), cht_height), is_permutation); @*/
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

            //@ list<int> chunk = chunk(p_in, i * cht_height, i * cht_height + j);
            //@ list<int> chunk_append = list_append(chunk, snd(new_elem));
            //@ list< pair<int, int> > chunk_append_ziped = zip_with_index(chunk_append);

            //@ list< pair<int, int> > chunk_ziped = zip_with_index(chunk);
            //@ list< pair<int, int> > chunk_ziped_append = list_append(chunk_ziped, new_elem);

            // Length of chunk
            //@ isolate_chunk_length(p_in, i * cht_height, i * cht_height + j);
            //@ append_length(chunk, snd(new_elem));

            // Append rule for zip_with_index
            //@ append_to_zip(chunk, snd(new_elem));
            //@ assert (chunk_append_ziped == chunk_ziped_append);

            // Preservation of fixpoint
            //@ append_preserves_fixpoint(chunk_ziped, new_elem, (is_modulo_permutation)(offset, shift, cht_height));
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
            //@ assume (chunk(update(((i*cht_height) + j), permut, p_in), i * cht_height, i * cht_height + j + 1) == chunk_append);//TODO
        }

        //@ mul_nonnegative(i, cht_height);
        //@ mul_bounds(cht_height, cht_height, i + 1, backend_capacity);
        //@ isolate_chunk_length(p, i * cht_height, (i + 1) * cht_height);
    }
    
    //@ open ints(permutations, cht_height*backend_capacity, ?p0);
    //@ close ints(permutations, cht_height*backend_capacity, p0);
    //@ list< list<int> > perms = list_split_every_n(p0, nat_of_int(backend_capacity), cht_height);
    //@ assume (true == forall(perms, is_permutation));

    int *next = malloc(sizeof(int) * (int)(cht_height));
    //@ assume(next != 0);//TODO: report failure
    //@ open ints(next, cht_height, ?n0);
    //@ close ints(next, cht_height, n0);
    for (uint32_t i = 0 ; i < cht_height ; ++i)
        /*@ invariant
                0 <= i &*& i <= cht_height &*&
                ints(next, cht_height, ?n) &*&
                true == forall(take(i, n), (is_cst)(0));
        @*/
    {
        next[i] = 0; 
        //@ list<int> updated_n = update(i, 0, n);
        //@ take_update_unrelevant(i, i, 0, n);
        //@ ints_to_nth(updated_n, n, i, 0);
        //@ append_take(updated_n, i, (is_cst)(0));
    }

    //@ open ints(next, cht_height, ?n);
    //@ close ints(next, cht_height, n);
    //@ assert (true == forall(n, (is_cst)(0)));
    
    for (uint32_t i = 0 ; i < cht_height ; ++i)
    /*@invariant true; @*/
    {
        for (uint32_t j = 0 ; j < backend_capacity ; ++j)
        /*@invariant true; @*/
        {
            uint32_t *value;

            uint32_t index = j * cht_height + i;
            int bucket_id = permutations[index];
            int priority = next[bucket_id];

            vector_borrow(cht, (int)(backend_capacity * bucket_id + priority), (void **)&value);
            *value = j;
            vector_return(cht, (int)(backend_capacity * bucket_id + priority), (void *)value);

            next[bucket_id] += 1;
        }
    }
    free(next);


    // Fill the priority lists for each hash in [0, cht_height)
    for (uint32_t i = 0; i < cht_height; ++i)
    /*@ invariant
            0 <= i &*& i <= cht_height &*&
            ints(permutations, cht_height*backend_capacity, p0) &*&
            vectorp<uint32_t>(cht, u_integer, ?vals, addrs) &*&
            length(vals) == cht_height*backend_capacity &*&
            true == forall(list_split_every_n(map(fst, vals), nat_of_int(i), backend_capacity), is_permutation) &*&
            true == forall(perms, is_permutation); @*/
    {
        uint32_t bknd = 0;
        uint32_t perm_pos = 0;
        //@ chunk_zerosize(map(fst, vals), i * backend_capacity);
        //@ is_sub_permutation(chunk(map(fst, vals), i * backend_capacity, i * backend_capacity), backend_capacity);        
        for (uint32_t j = 0; j < backend_capacity; ++j)
        /*@ invariant
                0 <= j &*& j <= backend_capacity &*&
                ints(permutations, cht_height*backend_capacity, p0) &*&
                vectorp<uint32_t>(cht, u_integer, ?new_vals, addrs) &*&
                length(new_vals) == cht_height*backend_capacity &*&
                bknd < backend_capacity &*&
                perm_pos < cht_height &*&
                true == is_sub_permutation(chunk(map(fst, new_vals), i * backend_capacity, i * backend_capacity + j), backend_capacity) &*&
                true == forall(perms, is_permutation); @*/
        {
            uint32_t *value;

            //@ mul_bounds(bknd, backend_capacity - 1, cht_height, cht_height);
            uint32_t index = bknd * cht_height + perm_pos;
            while (permutations[index] != (int)i)
            /*@ invariant 
                    ints(permutations, cht_height*backend_capacity, p0) &*&
                    bknd < backend_capacity &*&
                    perm_pos < cht_height &*&
                    index < backend_capacity * cht_height; @*/
            {
                ++bknd;
                if (backend_capacity <= bknd) {
                    bknd = 0;
                    ++perm_pos;
                    ////@ assume(perm_pos < cht_height);//TODO
                    assert(perm_pos < cht_height);
                }
                //@ mul_bounds(bknd, backend_capacity - 1, cht_height, cht_height);
                index = bknd * cht_height + perm_pos;
            }

            //@ mul_bounds(backend_capacity, backend_capacity, i, cht_height);
            //@ mul_bounds(backend_capacity, backend_capacity, i + 1, cht_height);
            vector_borrow(cht, (int)(backend_capacity * i + j), (void **)&value);
            //@ forall_nth(new_vals, is_one, backend_capacity*i + j);
            *value = bknd;
            vector_return(cht, (int)(backend_capacity * i + j), (void *)value);
            //@ forall_update(new_vals, is_one, backend_capacity*i + j, pair(bknd, 1.0));
            //@ append_take_nth_to_take(update(backend_capacity*i + j, pair(bknd, 1.0), new_vals), backend_capacity*i + j);
            //@ take_update_unrelevant(backend_capacity*i + j, backend_capacity*i + j, pair(bknd, 1.0), new_vals);
            //@ map_append(fst, take(backend_capacity*i + j, new_vals), cons(pair(bknd, 1.0), nil));
            //@ forall_append(map(fst, take(backend_capacity*i + j, new_vals)), cons(bknd, nil), (lt)(backend_capacity));
            //@ forall_append(map(fst, take(backend_capacity*i + j, new_vals)), cons(bknd, nil), (ge)(0));
            ++bknd;
            if (backend_capacity <= bknd) {
                bknd = 0;
                ++perm_pos;
                //@ assume(perm_pos < cht_height);//TODO
            }
        }
    }
    free(permutations);
    //@ assert vectorp<uint32_t>(cht, u_integer, ?values, addrs);
    //@ assume(valid_cht(values, backend_capacity, cht_height));//TODO
}

int cht_find_preferred_available_backend(uint64_t hash, struct Vector *cht, struct DoubleChain *active_backends, uint32_t cht_height, uint32_t backend_capacity, int *chosen_backend)
/*@ requires vectorp<uint32_t>(cht, u_integer, ?values, ?addrs) &*&
             double_chainp(?ch, active_backends) &*&
             *chosen_backend |-> _ &*&
             dchain_index_range_fp(ch) == backend_capacity &*&
             true == valid_cht(values, backend_capacity, cht_height); @*/
/*@ ensures vectorp<uint32_t>(cht, u_integer, values, addrs) &*&
            double_chainp(ch, active_backends) &*&
            *chosen_backend |-> ?chosen &*&
            (result == 0 ?
              false == cht_exists(hash, values, ch)        :
              true == cht_exists(hash, values, ch) &*&
              chosen == cht_choose(hash, values, ch) &*&
              result == 1 &*&
              0 <= chosen &*&
              chosen < dchain_index_range_fp(ch)); @*/
{
    uint64_t start = loop(hash, cht_height);
    for (uint32_t i = 0; i < backend_capacity; ++i)
    /*@ invariant 0 <= i &*& i <= backend_capacity &*&
                  vectorp<uint32_t>(cht, u_integer, values, addrs) &*&
                  cht_height*backend_capacity == length(values) &*&
                  double_chainp(ch, active_backends) &*&
                  true == forall(values, is_one) &*&
                  *chosen_backend |-> _ &*&
                  0 <= start &*& start < cht_height; @*/
    {
        //@ mul_bounds(start, cht_height, backend_capacity, backend_capacity);
        //@ mul_bounds(start+1, cht_height, backend_capacity, backend_capacity);
        //@ mul_bounds(cht_height, MAX_CHT_HEIGHT, backend_capacity, backend_capacity);
        uint64_t candidate_idx = start * backend_capacity + i; // There was a bug, right here, untill I tried to prove this.

        uint32_t *candidate;
        vector_borrow(cht, (int)candidate_idx, (void **)&candidate);

        //@ map_preserves_length(fst, values);
        //@ forall_nth(map(fst, values), (lt)(dchain_index_range_fp(ch)), candidate_idx);
        //@ nth_map(candidate_idx, fst, values);
        //@ forall_nth(map(fst, values), (ge)(0), candidate_idx);
        //@ update_id(candidate_idx, values);
        //@ forall_nth(values, is_one, candidate_idx);
        if (dchain_is_index_allocated(active_backends, (int)*candidate)) {
            *chosen_backend = (int)*candidate;
            vector_return(cht, (int)candidate_idx, candidate);
            //@ assume(cht_exists(hash, values, ch));//TODO
            //@ assert candidate |-> ?chosen_candidate;
            //@ assume(fst(nth(candidate_idx, values)) == cht_choose(hash, values, ch));//TODO
            return 1;
        }
        vector_return(cht, (int)candidate_idx, candidate);
    }
    //@ assume(!cht_exists(hash, values, ch));//TODO
    return 0;
}
