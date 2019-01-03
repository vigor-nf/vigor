#ifndef _FLOWMANAGER_H_INCLUDED_
#define _FLOWMANAGER_H_INCLUDED_

#include "nat_flow.h"
#include "lib/nf_time.h"

#include <stdbool.h>
#include <stdint.h>

struct FlowManager;

struct FlowManager* flow_manager_allocate(uint16_t starting_port,
                                          uint32_t nat_ip,
                                          uint16_t nat_device, /* NOTE: only required for verif to show that internal != external; can be removed once "our NAT" == router + "only NAT" */
                                          uint32_t expiration_time,
                                          uint64_t max_flows);

bool flow_manager_allocate_flow(struct FlowManager* manager, struct FlowId* id, uint16_t internal_device, time_t time, struct Flow* out_flow);
void flow_manager_expire(struct FlowManager* manager, time_t time);
bool flow_manager_get_internal(struct FlowManager* manager, struct FlowId* id, time_t time, struct Flow* out_flow);
bool flow_manager_get_external(struct FlowManager* manager, struct FlowId* id, time_t time, struct Flow* out_flow);

#ifdef KLEE_VERIFICATION
struct DoubleChain** flow_manager_get_chain(struct FlowManager* manager);
struct Map** flow_manager_get_in_table(struct FlowManager* manager);
struct Vector** flow_manager_get_in_keys(struct FlowManager* manager);
struct Vector** flow_manager_get_in_values(struct FlowManager* manager);
#endif

#endif //_FLOWMANAGER_H_INCLUDED_
