from state import flow_emap, int_devices
EXP_TIME = 10 * 1000
EXT_DEVICE = 1

if a_packet_received:
    flow_emap.expire_all(now - EXP_TIME)

h3 = pop_header(tcpudp, on_mismatch=([],[]))
h2 = pop_header(ipv4, on_mismatch=([],[]))
h1 = pop_header(ether, on_mismatch=([],[]))

if received_on_port == EXT_DEVICE:
    internal_flow = FlowIdc(h3.dst_port, h3.src_port, h2.daddr, h2.saddr, h2.npid)
    if flow_emap.has(internal_flow):
        flow_emap.refresh_idx(flow_emap.get(internal_flow), now)
    else:
        pass
else:
    internal_flow = FlowIdc(h3.src_port, h3.dst_port, h2.saddr, h2.daddr, h2.npid)
    if flow_emap.has(internal_flow):
        flow_emap.refresh_idx(flow_emap.get(internal_flow), now)
    else:
        pass
