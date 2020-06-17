from state import flow_emap, dyn_vals
WAN_DEVICE = 0
BURST = 3750000000
RATE = 375000000
EXP_TIME = 10 * 1000 * 1000 * 1000

h2 = pop_header(ipv4, on_mismatch=([],[]))
# Malformed IPv4
if (h2.vihl & 15) < 5 or packet_size - 14 < (((h2.len & 0xFF) << 8) | ((h2.len & 0xFF00) >> 8)):
    return ([],[])

h1 = pop_header(ether, on_mismatch=([],[]))

flow_emap.expire_all(now - EXP_TIME)

if received_on_port == WAN_DEVICE and flow_emap.has(ip_addrc(h2.daddr)):
    flow_idx = flow_emap.get(ip_addrc(h2.daddr))
    flow_emap.refresh_idx(flow_idx, now)
    flow = dyn_vals.get(flow_idx)
    bucket_size = flow.bucket_size + (now - flow.bucket_time)*RATE
    if BURST < bucket_size:
        bucket_size = BURST
    if bucket_size <= packet_size:
        dyn_vals.set(flow_idx, DynamicValuec(bucket_size, now))
        return ([],[]) # The packet surpasses the limit
    else:
        pass
else:
    pass
