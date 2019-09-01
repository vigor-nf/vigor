#ifndef _FLOWMANAGER_H_INCLUDED_
#define _FLOWMANAGER_H_INCLUDED_

#include "flow.h.gen.h"
#include "libvig/verified/vigor-time.h"

#include <stdbool.h>
#include <stdint.h>

struct FlowManager;

struct FlowManager *flow_manager_allocate(uint16_t fw_device,
                                          vigor_time_t expiration_time,
                                          uint64_t max_flows);

void flow_manager_allocate_or_refresh_flow(struct FlowManager *manager,
                                           struct FlowId *id,
                                           uint32_t internal_device,
                                           vigor_time_t time);
void flow_manager_expire(struct FlowManager *manager, vigor_time_t time);
bool flow_manager_get_refresh_flow(struct FlowManager *manager,
                                   struct FlowId *id, vigor_time_t time,
                                   uint32_t *internal_device);

#endif //_FLOWMANAGER_H_INCLUDED_
