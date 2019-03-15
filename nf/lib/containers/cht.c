#include "cht.h"
#include <assert.h>
#include <stdlib.h>

//@ #include "prime.gh"

static uint64_t loop(uint64_t k, uint64_t capacity)
//@ requires 0 < capacity &*& capacity < INT_MAX;
/*@ ensures 0 <= result &*& result < capacity &*& result == k%capacity; @*/
{
    uint64_t g = k % capacity;
    //@ div_mod_gt_0(g, k, capacity);
    return g;
}

/*@

    predicate sub_permut(list<int> xs, int max_val) =
                xs == nil ?
                        true
                :
                        true == forall(xs, (lt)(max_val)) &*&
                        true == forall(xs, (ge)(0)) &*&
                        true == no_dups(xs);


        fixpoint list<t> sub_list<t>(list<t> xs, int size) {
                switch(xs) {
                        case nil: return nil;
                        case cons(x0, xs0): return (size <= 0 ? nil : cons(x0, sub_list(xs0, size - 1)) );
                }
        }

        lemma void sub_list_zerosize<t>(list<t> xs)
                requires true;
                ensures sub_list(xs, 0) == nil;
        {
                switch(xs) {
                        case nil: assert (sub_list(xs, 0) == nil);
                        case cons(x0, xs0): assert (sub_list(xs, 0) == nil);
                }
        }
@*/

void cht_fill_cht(struct Vector *cht, uint32_t cht_height, uint32_t backend_capacity)
/*@ requires vectorp<uint32_t>(cht, u_integer, ?old_values, ?addrs) &*&
             0 < cht_height &*& cht_height < MAX_CHT_HEIGHT &*& prime(cht_height) &*&
             0 < backend_capacity &*& backend_capacity < cht_height &*&
             sizeof(int)*MAX_CHT_HEIGHT*backend_capacity < INT_MAX &*&
             length(old_values) == cht_height*backend_capacity &*&
             true == forall(old_values, is_one); @*/
/*@ ensures vectorp<uint32_t>(cht, u_integer, ?values, addrs) &*&
            true == valid_cht(values, backend_capacity, cht_height) &*&
            prime(cht_height); @*/
{
    // Make sure cht_height is prime.
    // for (int i = 2; i*i <= cht_height; ++i)
    ///*@ invariant true; @*/
    //{
    //  assert(i*(cht_height/i) != cht_height);
    //}

    // assert(backend_capacity < cht_height);

    //@ mul_bounds(sizeof(int), sizeof(int), cht_height, MAX_CHT_HEIGHT);
    //@ mul_bounds(sizeof(int)*cht_height, sizeof(int)*MAX_CHT_HEIGHT, backend_capacity, backend_capacity);
    //@ mul_nonzero(sizeof(int)*cht_height, backend_capacity);

    //@ assert(0 < sizeof(int)*cht_height*backend_capacity);
    //@ assert(sizeof(int)*cht_height*backend_capacity < INT_MAX);

    // Generate the permutations of 0..(cht_height - 1) for each backend
    int *permutations = malloc(sizeof(int) * (int)(cht_height * backend_capacity));
    //@ assume(permutations != 0);//TODO: report failure
    for (uint32_t i = 0; i < backend_capacity; ++i)
    /*@ invariant 0 <= i &*& i <= backend_capacity &*&
                  vectorp<uint32_t>(cht, u_integer, old_values, addrs) &*&
                  ints(permutations, cht_height*backend_capacity, _); @*/
    {
        uint32_t offset_absolut = i * 31;
        uint64_t offset = loop(offset_absolut, cht_height);
        uint64_t base_shift = loop(i, cht_height - 1);
        uint64_t shift = base_shift + 1;
        for (uint32_t j = 0; j < cht_height; ++j)
        /*@ invariant 0 <= j &*& j <= cht_height &*&
                      vectorp<uint32_t>(cht, u_integer, old_values, addrs) &*&
                      ints(permutations, cht_height*backend_capacity, _); @*/
        {
            //@ mul_bounds(cht_height, MAX_CHT_HEIGHT, i, backend_capacity);
            //@ mul_bounds(cht_height, MAX_CHT_HEIGHT, i + 1, backend_capacity);
            //@ mul_bounds(shift, MAX_CHT_HEIGHT, j, MAX_CHT_HEIGHT);
            uint64_t permut = loop(offset + shift * j, cht_height);
            //@ mul_bounds(i, backend_capacity - 1, cht_height, cht_height);

            permutations[i * cht_height + j] = (int)permut;
        }
    }
    // Fill the priority lists for each hash in [0, cht_height)
    for (uint32_t i = 0; i < cht_height; ++i)
    /*@ invariant ints(permutations, cht_height*backend_capacity, _) &*&
                  vectorp<uint32_t>(cht, u_integer, ?vals, addrs) &*&
                  0 <= i &*& i <= cht_height &*&
                  length(vals) == cht_height*backend_capacity &*&
                  true == forall(vals, is_one) &*&
                  true == forall(map(fst, take(i*backend_capacity, vals)), (lt)(backend_capacity)) &*&
                  true == forall(map(fst, take(i*backend_capacity, vals)), (ge)(0)); @*/
    {
        uint32_t bknd = 0;
        uint32_t perm_pos = 0;
        for (uint32_t j = 0; j < backend_capacity; ++j)
        /*@ invariant ints(permutations, cht_height*backend_capacity, _) &*&
                      vectorp<uint32_t>(cht, u_integer, ?new_vals, addrs) &*&
                      bknd < backend_capacity &*&
                      perm_pos < cht_height &*&
                      0 <= j &*& j <= backend_capacity &*&
                      length(new_vals) == cht_height*backend_capacity &*&
                      true == forall(new_vals, is_one) &*&
                      true == forall(map(fst, take(i*backend_capacity + j, new_vals)), (lt)(backend_capacity)) &*&
                      true == forall(map(fst, take(i*backend_capacity + j, new_vals)), (ge)(0)); @*/
        {
            uint32_t *value;
            //@ mul_bounds(bknd, backend_capacity - 1, cht_height, cht_height);
            uint32_t row = bknd * cht_height;
            uint32_t index = row + perm_pos;
            while (permutations[index] != (int)i)
            /*@ invariant ints(permutations, cht_height*backend_capacity, _) &*&
                          vectorp<uint32_t>(cht, u_integer, new_vals, addrs) &*&
                          bknd < backend_capacity &*&
                          perm_pos < cht_height; @*/
            {
                ++bknd;
                if (backend_capacity <= bknd) {
                    bknd = 0;
                    ++perm_pos;
                    //@ assume(perm_pos < cht_height);//TODO
                    assert(perm_pos < cht_height);
                }
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

int cht_find_preferred_available_backend(uint64_t hash, struct Vector *cht, struct DoubleChain *active_backends, uint32_t cht_height, uint32_t backend_capacity,
                                         int *chosen_backend)
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
