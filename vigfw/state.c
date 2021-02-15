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
bool int_dev_bounds(void* value, int index, void* state) {
  uint32_t v = *(uint32_t*)value;
  return (v < 2) AND
        (v != 1);
}
struct State* alloc_state(int max_flows, uint32_t fw_device)
{
  if (allocated_nf_state != NULL) return allocated_nf_state;
  struct State* ret = malloc(sizeof(struct State));
  if (ret == NULL) return NULL;
  ret->fm = NULL;
  if (map_allocate(FlowId_eq, FlowId_hash, max_flows, &(ret->fm)) == 0) return NULL;
  ret->fv = NULL;
  if (vector_allocate(sizeof(struct FlowId), max_flows, FlowId_allocate, &(ret->fv)) == 0) return NULL;
  ret->int_devices = NULL;
  if (vector_allocate(sizeof(uint32_t), max_flows, null_init, &(ret->int_devices)) == 0) return NULL;
  ret->heap = NULL;
  if (dchain_allocate(max_flows, &(ret->heap)) == 0) return NULL;
  ret->max_flows = max_flows;
  ret->fw_device = fw_device;
#ifdef KLEE_VERIFICATION
  map_set_layout(ret->fm, FlowId_descrs, sizeof(FlowId_descrs)/sizeof(FlowId_descrs[0]), FlowId_nests, sizeof(FlowId_nests)/sizeof(FlowId_nests[0]), "FlowId");
  vector_set_layout(ret->fv, FlowId_descrs, sizeof(FlowId_descrs)/sizeof(FlowId_descrs[0]), FlowId_nests, sizeof(FlowId_nests)/sizeof(FlowId_nests[0]), "FlowId");
  vector_set_layout(ret->int_devices, NULL, 0, NULL, 0, "uint32_t");
  vector_set_entry_condition(ret->int_devices, int_dev_bounds, ret);
#endif//KLEE_VERIFICATION
  allocated_nf_state = ret;
  return ret;
}

#ifdef KLEE_VERIFICATION
void nf_loop_iteration_border(unsigned lcore_id, vigor_time_t time) {
  loop_iteration_border(&allocated_nf_state->fm,
                        &allocated_nf_state->fv,
                        &allocated_nf_state->int_devices,
                        &allocated_nf_state->heap,
                        allocated_nf_state->max_flows,
                        allocated_nf_state->fw_device,
                        lcore_id,
                        time);
}

#endif//KLEE_VERIFICATION
