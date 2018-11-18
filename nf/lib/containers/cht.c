#include <stdlib.h>
#include <assert.h>
#include "cht.h"


void
cht_fill_cht(struct Vector* cht, int cht_height, int backend_capacity)
/*@ requires vectorp<uint32_t>(cht, ?entp, ?values, ?addrs); @*/
/*@ ensures vectorp<uint32_t>(cht, entp, values, addrs); @*/
{
  //@ assume(false);//TODO
  //Make sure cht_height is prime.
  for (int i = 2; i*i <= cht_height; ++i)
  /*@ invariant true; @*/
  {
    assert(i*(cht_height/i) != cht_height);
  }

  assert(backend_capacity < cht_height);

  // Generate the permutations of 0..(cht_height - 1) for each backend
  int* permutations = malloc(sizeof(int)*cht_height*(backend_capacity + 1));
  for (int i = 0; i < backend_capacity; ++i)
  /*@ invariant true; @*/
  {
    int offset = (i*31)%cht_height;
    int shift = i%cht_height + 1;
    for (int j = 0; j < cht_height; ++j)
    /*@ invariant true; @*/
    {
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
        //printf("%02d ", permutations[bknd*cht_height + perm_pos]);
        ++bknd;
        if (backend_capacity <= bknd) {
          //printf("..\n");
          bknd = 0;
          ++perm_pos;
          assert(perm_pos < cht_height);
        }
      }
      //printf("** ");
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
  //printf("preferences:\n");
  //for (int i = 0; i < cht_height; ++i) {
  //  for (int j = 0; j < backend_capacity; ++j) {
  //    uint32_t* value;
  //    vector_borrow(cht, i*backend_capacity + j, (void**)&value);
  //    printf("%02d, ", *value);
  //    vector_return(cht, i*backend_capacity + j, (void*)value);
  //  }
  //  printf("\n");
  //}
  free(permutations);
}

int
cht_find_preferred_available_backend(uint64_t hash, struct Vector* cht,
                                     struct DoubleChain* active_backends,
                                     uint32_t cht_height,
                                     uint32_t backend_capacity,
                                     int *chosen_backend)
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
{
  //@ assume(false);//TODO
  for (int i = 0; i < backend_capacity; ++i)
  /*@ invariant true; @*/
  {

    int candidate_idx = (hash + i) % cht_height;

    int* candidate;
    vector_borrow(cht, candidate_idx, (void**)&candidate);
    //printf("%d:%d ", candidate_idx, *candidate);

    if (dchain_is_index_allocated(active_backends, *candidate)) {
      *chosen_backend = *candidate;
      vector_return(cht, candidate_idx, candidate);
      //printf("FOUND\n");
      return 1;
    }
    vector_return(cht, candidate_idx, candidate);
  }
  //printf("give up\n");
  return 0;
}
