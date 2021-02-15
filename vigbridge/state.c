#include "state.h"
#include <stdlib.h>
#include "libvig/verified/boilerplate-util.h"
#ifdef KLEE_VERIFICATION
#include "libvig/models/verified/double-chain-control.h"
#include "libvig/models/verified/ether.h"
#include "libvig/models/verified/map-control.h"
#include "libvig/models/verified/vector-control.h"
#include "libvig/models/verified/lpm-dir-24-8-control.h"
#endif//KLEE_VERIFICATION
struct State* allocated_nf_state = NULL;
bool dyn_val_condition(void* value, int index, void* state) {
  struct DynamicValue *v = value;
  return (0 <= v->device) AND
        (v->device < 2);
}
bool stat_map_condition(void* value, int index, void* state) {
  struct StaticKey *v = value;
  return (0 <= index) AND
        (index < 2);
}
struct State* alloc_state(uint32_t capacity, uint32_t stat_capacity, uint32_t dev_count)
{
  if (allocated_nf_state != NULL) return allocated_nf_state;
  struct State* ret = malloc(sizeof(struct State));
  if (ret == NULL) return NULL;
  ret->dyn_map = NULL;
  if (map_allocate(rte_ether_addr_eq, rte_ether_addr_hash, capacity, &(ret->dyn_map)) == 0) return NULL;
  ret->dyn_keys = NULL;
  if (vector_allocate(sizeof(struct rte_ether_addr), capacity, rte_ether_addr_allocate, &(ret->dyn_keys)) == 0) return NULL;
  ret->dyn_vals = NULL;
  if (vector_allocate(sizeof(struct DynamicValue), capacity, DynamicValue_allocate, &(ret->dyn_vals)) == 0) return NULL;
  ret->st_map = NULL;
  if (map_allocate(StaticKey_eq, StaticKey_hash, stat_capacity, &(ret->st_map)) == 0) return NULL;
  ret->st_vec = NULL;
  if (vector_allocate(sizeof(struct StaticKey), stat_capacity, StaticKey_allocate, &(ret->st_vec)) == 0) return NULL;
  ret->dyn_heap = NULL;
  if (dchain_allocate(capacity, &(ret->dyn_heap)) == 0) return NULL;
  ret->capacity = capacity;
  ret->stat_capacity = stat_capacity;
  ret->dev_count = dev_count;
#ifdef KLEE_VERIFICATION
  map_set_layout(ret->dyn_map, rte_ether_addr_descrs, sizeof(rte_ether_addr_descrs)/sizeof(rte_ether_addr_descrs[0]), rte_ether_addr_nests, sizeof(rte_ether_addr_nests)/sizeof(rte_ether_addr_nests[0]), "rte_ether_addr");
  vector_set_layout(ret->dyn_keys, rte_ether_addr_descrs, sizeof(rte_ether_addr_descrs)/sizeof(rte_ether_addr_descrs[0]), rte_ether_addr_nests, sizeof(rte_ether_addr_nests)/sizeof(rte_ether_addr_nests[0]), "rte_ether_addr");
  vector_set_layout(ret->dyn_vals, DynamicValue_descrs, sizeof(DynamicValue_descrs)/sizeof(DynamicValue_descrs[0]), DynamicValue_nests, sizeof(DynamicValue_nests)/sizeof(DynamicValue_nests[0]), "DynamicValue");
  vector_set_entry_condition(ret->dyn_vals, dyn_val_condition, ret);
  map_set_layout(ret->st_map, StaticKey_descrs, sizeof(StaticKey_descrs)/sizeof(StaticKey_descrs[0]), StaticKey_nests, sizeof(StaticKey_nests)/sizeof(StaticKey_nests[0]), "StaticKey");
  map_set_entry_condition(ret->st_map, stat_map_condition, ret);
  vector_set_layout(ret->st_vec, StaticKey_descrs, sizeof(StaticKey_descrs)/sizeof(StaticKey_descrs[0]), StaticKey_nests, sizeof(StaticKey_nests)/sizeof(StaticKey_nests[0]), "StaticKey");
#endif//KLEE_VERIFICATION
  allocated_nf_state = ret;
  return ret;
}

#ifdef KLEE_VERIFICATION
void nf_loop_iteration_border(unsigned lcore_id, vigor_time_t time) {
  loop_iteration_border(&allocated_nf_state->dyn_map,
                        &allocated_nf_state->dyn_keys,
                        &allocated_nf_state->dyn_vals,
                        &allocated_nf_state->st_map,
                        &allocated_nf_state->st_vec,
                        &allocated_nf_state->dyn_heap,
                        allocated_nf_state->capacity,
                        allocated_nf_state->stat_capacity,
                        allocated_nf_state->dev_count,
                        lcore_id,
                        time);
}

#endif//KLEE_VERIFICATION
