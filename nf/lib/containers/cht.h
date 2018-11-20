#ifndef _CHT_H_INCLUDED_
#define _CHT_H_INCLUDED_

#include "lib/containers/vector.h"
#include "lib/containers/double-chain.h"

#define MAX_CHT_HEIGHT 1000000

/*@
  fixpoint bool valid_cht(list<pair<int, real> > values, uint32_t backend_capacity, uint32_t cht_height) {
    return cht_height == length(values) &&
           0 < cht_height &&
           cht_height < MAX_CHT_HEIGHT &&
           backend_capacity < INT_MAX &&
           true == forall(map(fst, values), (lt)(backend_capacity)) &&
           true == forall(map(fst, values), (ge)(0));
  }
@*/

void cht_fill_cht(struct Vector* cht,
                  int cht_height,
                  int backend_capacity);
/*@ requires vectorp<uint32_t>(cht, ?entp, _, ?addrs) &*&
             0 < cht_height &*& cht_height < MAX_CHT_HEIGHT &*&
             0 < backend_capacity &*& backend_capacity < cht_height; @*/
/*@ ensures vectorp<uint32_t>(cht, entp, ?values, addrs) &*&
            true == valid_cht(values, backend_capacity, cht_height); @*/

int
cht_find_preferred_available_backend(uint64_t hash, struct Vector* cht,
                                     struct DoubleChain* active_backends,
                                     uint32_t cht_height,
                                     uint32_t backend_capacity,
                                     int *chosen_backend);
/*@ requires vectorp<uint32_t>(cht, u_integer, ?values, ?addrs) &*&
             double_chainp(?ch, active_backends) &*&
             *chosen_backend |-> _ &*&
             dchain_index_range_fp(ch) == backend_capacity &*&
             true == valid_cht(values, backend_capacity, cht_height); @*/
/*@ ensures vectorp<uint32_t>(cht, u_integer, values, addrs) &*&
            double_chainp(ch, active_backends) &*&
            *chosen_backend |-> ?chosen &*&
            (result == 0 ?
              true        :
              result == 1 &*&
              0 <= chosen &*&
              chosen < dchain_index_range_fp(ch)); @*/

#endif//_CHT_H_INCLUDED_
