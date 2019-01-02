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
cht_fill_cht(struct Vector* cht, uint32_t cht_height, uint32_t backend_capacity)
/*@ requires vectorp<uint32_t>(cht, u_integer, ?old_values, ?addrs) &*&
             0 < cht_height &*& cht_height < MAX_CHT_HEIGHT &*&
             MAX_CHT_HEIGHT*backend_capacity < INT_MAX &*&
             sizeof(int)*MAX_CHT_HEIGHT*(backend_capacity + 1) < INT_MAX &*&
             0 < backend_capacity &*& backend_capacity < cht_height &*&
             length(old_values) == cht_height*backend_capacity &*&
             true == forall(old_values, is_one); @*/
/*@ ensures vectorp<uint32_t>(cht, u_integer, ?values, addrs) &*&
            true == valid_cht(values, backend_capacity, cht_height); @*/
{
  //Make sure cht_height is prime.
  //for (int i = 2; i*i <= cht_height; ++i)
  ///*@ invariant true; @*/
  //{
  //  assert(i*(cht_height/i) != cht_height);
  //}

  //assert(backend_capacity < cht_height);
 
  
  //@ mul_bounds(sizeof(int), sizeof(int), cht_height, MAX_CHT_HEIGHT);
  //@ mul_bounds(sizeof(int)*cht_height, sizeof(int)*MAX_CHT_HEIGHT, backend_capacity + 1, backend_capacity + 1);
  //@ assert((int)sizeof(int)*cht_height*(backend_capacity + 1) < INT_MAX);//TODO
  //@ assert(0 < (int)sizeof(int)*cht_height*(backend_capacity + 1));//TODO

  // Generate the permutations of 0..(cht_height - 1) for each backend
  int* permutations = malloc(sizeof(int)*(int)(cht_height*(backend_capacity + 1)));
  //@ assume(permutations != 0);//TODO: report failure
  for (uint32_t i = 0; i < backend_capacity; ++i)
  /*@ invariant 0 <= i &*& i <= backend_capacity &*&
                vectorp<uint32_t>(cht, u_integer, old_values, addrs) &*&
                ints(permutations, cht_height*(backend_capacity + 1), _); @*/
  {
    uint32_t offset_absolut = i*31;
    uint64_t offset = loop(offset_absolut, cht_height);
    uint64_t base_shift = loop(i, cht_height);
    uint64_t shift = base_shift + 1;
    for (uint32_t j = 0; j < cht_height; ++j)
    /*@ invariant 0 <= j &*& j <= cht_height &*&
                  vectorp<uint32_t>(cht, u_integer, old_values, addrs) &*&
                  ints(permutations, cht_height*(backend_capacity + 1), _); @*/
    {
      //@ mul_bounds(cht_height, MAX_CHT_HEIGHT, i, backend_capacity);
      //@ mul_bounds(cht_height, MAX_CHT_HEIGHT, i + 1, backend_capacity);
      //@ mul_bounds(shift, MAX_CHT_HEIGHT, j, MAX_CHT_HEIGHT);
      uint64_t permut = loop(offset + shift*j, cht_height);
      //@ mul_bounds(i, backend_capacity, cht_height, cht_height);
      permutations[i*cht_height + j] = (int)permut;
    }
  }
  // Fill the priority lists for each hash in [0, cht_height)
  for (uint32_t i = 0; i < cht_height; ++i)
  /*@ invariant ints(permutations, cht_height*(backend_capacity + 1), _) &*&
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
    /*@ invariant ints(permutations, cht_height*(backend_capacity + 1), _) &*&
                  vectorp<uint32_t>(cht, u_integer, ?new_vals, addrs) &*&
                  bknd < backend_capacity &*&
                  perm_pos < cht_height &*&
                  0 <= j &*& j <= backend_capacity &*&
                  length(new_vals) == cht_height*backend_capacity &*&
                  true == forall(new_vals, is_one) &*&
                  true == forall(map(fst, take(i*backend_capacity + j, new_vals)), (lt)(backend_capacity)) &*&
                  true == forall(map(fst, take(i*backend_capacity + j, new_vals)), (ge)(0)); @*/
    {
      uint32_t* value;
      //@ mul_bounds(bknd, backend_capacity, cht_height, MAX_CHT_HEIGHT);
      //@ mul_bounds(bknd, backend_capacity, cht_height, cht_height);
      uint32_t row = bknd*cht_height;
      uint32_t index = row + perm_pos;
      while (permutations[index] != (int)i)
      /*@ invariant ints(permutations, cht_height*(backend_capacity + 1), _) &*&
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
      vector_borrow(cht, (int)(backend_capacity*i + j), (void**)&value);
      //@ forall_nth(new_vals, is_one, backend_capacity*i + j);
      *value = bknd;
      vector_return(cht, (int)(backend_capacity*i + j), (void*)value);
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
                cht_height*backend_capacity == length(values) &*&
                double_chainp(ch, active_backends) &*&
                *chosen_backend |-> _ &*&
                0 <= start &*& start < cht_height; @*/
  {
    //@ mul_bounds(start, cht_height, backend_capacity, backend_capacity);
    //@ mul_bounds(start+1, cht_height, backend_capacity, backend_capacity);
    //@ mul_bounds(cht_height, MAX_CHT_HEIGHT, backend_capacity, backend_capacity);
    uint64_t candidate_idx = start*backend_capacity + i; //There was a bug, right here, untill I tried to prove this.

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