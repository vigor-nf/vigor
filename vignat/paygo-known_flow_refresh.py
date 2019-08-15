from state import flow_emap
EXP_TIME = 10 * 1000
EXT_IP_ADDR = ext_ip
EXT_PORT = 1
if a_packet_received:
    flow_emap.expire_all(now - EXP_TIME)
h3 = pop_header(tcpudp, on_mismatch=([],[]))
h2 = pop_header(ipv4, on_mismatch=([],[]))
h1 = pop_header(ether, on_mismatch=([],[]))

internal_flow_id = FlowIdc(h3.src_port, h3.dst_port, h2.saddr, h2.daddr, received_on_port, h2.npid)
if received_on_port != EXT_PORT and flow_emap.has(internal_flow_id) :
    idx = flow_emap.get(internal_flow_id)
    flow_emap.refresh_idx(idx, now)
    return ([EXT_PORT],
            [ether(h1, saddr=..., daddr=...),
             ipv4(h2, cksum=..., saddr=EXT_IP_ADDR),
             tcpudp(h3, src_port=idx + start_port)])
else:
    pass
