#include <stdlib.h>
#include <assert.h>
#include "cht.h"

//@ #include "modulo.gh"

static
uint64_t loop(uint64_t k, uint64_t capacity)
//@ requires 0 < capacity &*& 2*capacity < INT_MAX;
/*@ ensures 0 <= result &*& result < capacity &*&
  result == loop_fp(k, capacity); @*/
{
  uint64_t g = k%capacity;
  //@ div_mod(g, k, capacity);
  //@ assert(2*capacity< INT_MAX);

  //FIXME: this step is unnecessary and expensive.
  // It was semantically justified for negitive numbers.
  // However, once we switched to unsigned hashes, it is just an expensive
  // identity function. Remove it.

  uint64_t res = (g + capacity)%capacity;
  //@ div_mod_gt_0(res, g + capacity, capacity);
  return res;
}

void
cht_fill_cht(struct Vector* cht, int cht_height, int backend_capacity)
/*@ requires vectorp<uint32_t>(cht, ?entp, _, ?addrs) &*&
             0 < cht_height &*& cht_height < MAX_CHT_HEIGHT &*&
             0 < backend_capacity &*& backend_capacity < cht_height; @*/
/*@ ensures vectorp<uint32_t>(cht, entp, ?values, addrs) &*&
            true == valid_cht(values, backend_capacity, cht_height); @*/
{
  //Make sure cht_height is prime.
  //for (int i = 2; i*i <= cht_height; ++i)
  ///*@ invariant true; @*/
  //{
  //  assert(i*(cht_height/i) != cht_height);
  //}

  assert(backend_capacity < cht_height);
  //@ assume(false);//TODO
  
  //@ assume((int)sizeof(int)*cht_height*(backend_capacity + 1) < INT_MAX);//TODO
  //@ assume(0 < (int)sizeof(int)*cht_height*(backend_capacity + 1));//TODO

  // Generate the permutations of 0..(cht_height - 1) for each backend
  int* permutations = malloc((int)sizeof(int)*cht_height*(backend_capacity + 1));
  for (int i = 0; i < backend_capacity; ++i)
  /*@ invariant 0 <= i &*& i < backend_capacity; @*/
  {
    int offset = (i*31)%cht_height;
    //@ assume(0 <= i%cht_height); //TODO
    //@ assume(i%cht_height < cht_height);//TODO
    int shift = i%cht_height + 1;
    for (int j = 0; j < cht_height; ++j)
    /*@ invariant 0 <= j &*& j < cht_height; @*/
    {
      //@ assume(0 <= i*cht_height); //TODO
      permutations[i*cht_height + j] = (offset + shift*j)%cht_height;
      //printf("%d, ", permutations[i*cht_height + j]);
    }
    //printf("\n");
  }
  // Fill the priority lists for each hash in [0, cht_height)
  for (int i = 0; i < cht_height; ++i)
  /*@ invariant true; @*/
  {
    int bknd = 0;
    int perm_pos = 0;
    //printf("looking for %d\n", i);
    for (int j = 0; j < backend_capacity; ++j)
    /*@ invariant true; @*/
    {
      assert(perm_pos < cht_height);
      while (permutations[bknd*cht_height + perm_pos] != i)
      /*@ invariant true; @*/
      {
        ++bknd;
        if (backend_capacity <= bknd) {
          bknd = 0;
          ++perm_pos;
          assert(perm_pos < cht_height);
        }
      }
      uint32_t* value;
      vector_borrow(cht, i*backend_capacity + j, (void**)&value);
      *value = bknd;
      vector_return(cht, i*backend_capacity + j, (void*)value);
      ++bknd;
      if (backend_capacity <= bknd) {
        bknd = 0;
        ++perm_pos;
      }
    }
  }
  free(permutations);
}

int
cht_find_preferred_available_backend(uint64_t hash, struct Vector* cht,
                                     struct DoubleChain* active_backends,
                                     uint32_t cht_height,
                                     uint32_t backend_capacity,
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
              true        :
              result == 1 &*&
              0 <= chosen &*&
              chosen < dchain_index_range_fp(ch)); @*/
{
  uint64_t start = loop(hash, cht_height);
  for (uint32_t i = 0; i < backend_capacity; ++i)
  /*@ invariant 0 <= i &*& i <= backend_capacity &*&
                vectorp<uint32_t>(cht, u_integer, values, addrs) &*&
                cht_height == length(values) &*&
                double_chainp(ch, active_backends) &*&
                *chosen_backend |-> _ &*&
                0 <= start &*& start < cht_height; @*/
  {
    uint64_t candidate_idx = loop(start + i, cht_height);

    uint32_t* candidate;
    vector_borrow(cht, (int)candidate_idx, (void**)&candidate);
    
    //@ map_preserves_length(fst, values);
    //@ forall_nth(map(fst, values), (lt)(dchain_index_range_fp(ch)), candidate_idx);
    //@ nth_map(candidate_idx, fst, values);
    //@ forall_nth(map(fst, values), (ge)(0), candidate_idx);
    //@ update_id(candidate_idx, values);
    if (dchain_is_index_allocated(active_backends, (int)*candidate)) {
      *chosen_backend = (int)*candidate;
      vector_return(cht, (int)candidate_idx, candidate);
      return 1;
    }
    vector_return(cht, (int)candidate_idx, candidate);
  }
  return 0;
}
