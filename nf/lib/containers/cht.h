#ifndef _CHT_H_INCLUDED_
#define _CHT_H_INCLUDED_

#include "lib/containers/vector.h"
#include "lib/containers/double-chain.h"

void cht_fill_cht(struct Vector* cht,
                  int cht_height,
                  int backend_capacity);
/*@ requires vectorp<uint32_t>(cht, ?entp, ?values, ?addrs); @*/
/*@ ensures vectorp<uint32_t>(cht, entp, values, addrs); @*/

int
cht_find_preferred_available_backend(uint64_t hash, struct Vector* cht,
                                     struct DoubleChain* active_backends,
                                     uint32_t cht_height,
                                     uint32_t backend_capacity,
                                     int *chosen_backend);
/*@ requires vectorp<uint32_t>(cht, ?entp, ?values, ?addrs) &*&
             double_chainp(?ch, active_backends) &*&
             *chosen_backend |-> _; @*/
/*@ ensures vectorp<uint32_t>(cht, entp, values, addrs) &*&
            double_chainp(ch, active_backends) &*&
            *chosen_backend |-> ?chosen &*&
            (result == 0 ?
              true        :
              result == 1 &*&
              0 <= chosen &*&
              chosen < dchain_index_range_fp(ch)); @*/

#endif//_CHT_H_INCLUDED_
