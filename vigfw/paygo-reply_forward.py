from state import flow_emap, int_devices
EXP_TIME = 10 * 1000
EXT_DEVICE = 1

if a_packet_received:
    flow_emap.expire_all(now - EXP_TIME)

h3 = pop_header(tcpudp, on_mismatch=([],[]))
h2 = pop_header(ipv4, on_mismatch=([],[]))
h1 = pop_header(ether, on_mismatch=([],[]))

internal_flow = FlowIdc(h3.dst_port, h3.src_port, h2.daddr, h2.saddr, h2.npid)
if received_on_port == EXT_DEVICE and flow_emap.has(internal_flow):
    fl_id = flow_emap.get(internal_flow)
    flow_emap.refresh_idx(fl_id, now)
    out_port = vector_get(int_devices, fl_id)
    return ([out_port],[ether(h1, saddr=..., daddr=...),
                        ipv4(h2, cksum=...),
                        tcpudp(h3)])
else:
    pass
