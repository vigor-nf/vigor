from state import flow_emap, dyn_vals
LAN_DEVICE = 1
WAN_DEVICE = 0
BURST = 3750000000
RATE = 375000000
EXP_TIME = 10 * 1000 * 1000 * 1000

h2 = pop_header(ipv4, on_mismatch=([],[]))
h1 = pop_header(ether, on_mismatch=([],[]))

# Malformed IPv4
if (h2.vihl & 15) < 5 or packet_size - 14 < (((h2.len & 0xFF) << 8) | ((h2.len & 0xFF00) >> 8)):
    return ([],[])

flow_emap.expire_all(now - EXP_TIME)

if received_on_port == LAN_DEVICE:
    return ([WAN_DEVICE],[ether(h1), ipv4(h2)])
else:
    if received_on_port == WAN_DEVICE:
        if flow_emap.has(ip_addrc(h2.daddr)):
            flow_idx = flow_emap.get(ip_addrc(h2.daddr))
            flow_emap.refresh_idx(flow_idx, now)
            flow = dyn_vals.get(flow_idx)
            bucket_size = 0
            if now - flow.bucket_time < EXP_TIME:
                bucket_size = flow.bucket_size + (now - flow.bucket_time)*RATE / 1000000000
                if BURST < bucket_size:
                    bucket_size = BURST
            else:
                bucket_size = BURST
            if packet_size < bucket_size:
                bucket_size = bucket_size - packet_size
                dyn_vals.set(flow_idx, DynamicValuec(bucket_size, now))
                return ([LAN_DEVICE], [ether(h1),ipv4(h2)])
            else:
                dyn_vals.set(flow_idx, DynamicValuec(bucket_size, now))
                return ([],[])
        else:
            if not flow_emap.full():
                flow_idx = the_index_allocated
                flow_emap.add(ip_addrc(h2.daddr), flow_idx, now)
                flow = DynamicValuec(BURST - packet_size, now)
                dyn_vals.set(flow_idx, flow)
                return ([LAN_DEVICE], [ether(h1), ipv4(h2)])
    else:
        return ([],[])

