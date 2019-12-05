#ifndef _CHT_H_INCLUDED_
#define _CHT_H_INCLUDED_

#include "libvig/verified/double-chain.h"
#include "libvig/verified/vector.h"

//@ #include "../proof/prime.gh"
//@ #include "../proof/permutations.gh"
//@ #include "../proof/listutils.gh"

// MAX_CHT_HEIGHT*MAX_CHT_HEIGHT < MAX_INT
#define MAX_CHT_HEIGHT 40000

/*@
    fixpoint bool valid_cht(list<pair<int, real> > values, uint32_t backend_capacity, uint32_t cht_height) {
        return
            cht_height*backend_capacity == length(values) &&
            0 < cht_height && cht_height < MAX_CHT_HEIGHT &&
            MAX_CHT_HEIGHT*backend_capacity < INT_MAX &&
            sizeof(int)*MAX_CHT_HEIGHT*(backend_capacity + 1) < INT_MAX &&
            0 < backend_capacity && backend_capacity < INT_MAX &&
            true == forall(values, is_one) &&
            true == forall(split(map(fst, values), nat_of_int(cht_height), backend_capacity), is_permutation);
    }

    fixpoint bool cht_exists(int hash, list<pair<int, real> > cht, dchain filter) {
        return exists(chunk(map(fst, cht), hash%(length(cht)/dchain_index_range_fp(filter)) * dchain_index_range_fp(filter), (hash%(length(cht)/dchain_index_range_fp(filter)) + 1) * dchain_index_range_fp(filter)), (dchain_allocated_fp)(filter));
    }


    fixpoint int cht_choose(int hash, list<pair<int, real> > cht, dchain filter) {
        return nth(hash%(length(cht)/dchain_index_range_fp(filter)) * dchain_index_range_fp(filter) + get_some(index_of_fp(chunk(map(fst, cht),hash%(length(cht)/dchain_index_range_fp(filter)) * dchain_index_range_fp(filter), (hash%(length(cht)/dchain_index_range_fp(filter)) + 1) * dchain_index_range_fp(filter)), 0, (dchain_allocated_fp)(filter))), map(fst, cht));
    }

@*/

int cht_fill_cht(struct Vector *cht, uint32_t cht_height, uint32_t backend_capacity);
/*@ requires
        vectorp<uint32_t>(cht, u_integer, ?old_values, ?addrs) &*&
        0 < cht_height &*& cht_height < MAX_CHT_HEIGHT &*& true == is_prime(cht_height) &*&
        0 < backend_capacity &*& backend_capacity < cht_height &*&
        sizeof(int)*MAX_CHT_HEIGHT*(backend_capacity + 1) < INT_MAX &*&
        length(old_values) == cht_height*backend_capacity &*&
        true == forall(old_values, is_one); @*/
/*@ ensures
        vectorp<uint32_t>(cht, u_integer, ?values, addrs) &*&
        (result != 0 ? true == valid_cht(values, backend_capacity, cht_height) : emp); @*/

int cht_find_preferred_available_backend(uint64_t hash, struct Vector *cht, struct DoubleChain *active_backends, uint32_t cht_height, uint32_t backend_capacity, int *chosen_backend);
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

#endif //_CHT_H_INCLUDED_
