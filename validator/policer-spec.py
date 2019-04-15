EXP_TIME = 10
LAN_DEVICE = 0
WAN_DEVICE = 1
BURST = 125000
RATE = 12500

h2 = pop_header(ipv4, on_mismatch=([],[]))
h1 = pop_header(ether, on_mismatch=([],[]))

if EXP_TIME <= now:
    flow_emap = emap_expire_all(flow_emap, now - EXP_TIME)

if received_on_port == LAN_DEVICE:
    return ([WAN_DEVICE],[ether(h1), ipv4(h2)])
else:
    if received_on_port == WAN_DEVICE:
        if emap_has(flow_emap, ip_addrc(h2.daddr)):
            flow_idx = emap_get(flow_emap, ip_addrc(h2.daddr))
            flow_emap = emap_refresh_idx(flow_emap, flow_idx, now)
            flow = vector_get(dyn_vals, flow_idx)
            bucket_size = flow.bucket_size + (now - flow.bucket_time)*RATE
            if BURST < bucket_size:
                bucket_size = BURST
            if packet_size < bucket_size:
                bucket_size = bucket_size - packet_size
                dyn_vals = vector_set(dyn_vals, flow_idx, DynamicValuec(bucket_size, now))
                return ([LAN_DEVICE], [ether(h1),ipv4(h2)])
            else:
                return ([],[])
        else:
            if not emap_full(flow_emap):
                flow_idx = the_index_allocated
                flow_emap = emap_add(flow_emap, ip_addrc(h2.daddr), flow_idx, now)
                flow = DynamicValuec(BURST - packet_size, now)
                dyn_vals = vector_set(dyn_vals, flow_idx, flow)
                return ([LAN_DEVICE], [ether(h1), ipv4(h2)])
    else:
        return ([],[])

