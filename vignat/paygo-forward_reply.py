from state import flow_emap
EXP_TIME = 10 * 1000
EXT_PORT = 1

if a_packet_received:
    flow_emap.expire_all(now - EXP_TIME)

h3 = pop_header(tcpudp, on_mismatch=([],[]))
h2 = pop_header(ipv4, on_mismatch=([],[]))
h1 = pop_header(ether, on_mismatch=([],[]))
flow_indx = h3.dst_port - start_port
if received_on_port == EXT_PORT and flow_emap.has_idx(flow_indx):
    internal_flow = flow_emap.get_key(flow_indx)
    flow_emap.refresh_idx(flow_indx, now)
    if (internal_flow.dip == h2.saddr and
        internal_flow.dp == h3.src_port and
        internal_flow.prot == h2.npid):
        return ([internal_flow.idev],
                [ether(h1, saddr=..., daddr=...),
                 ipv4(h2, cksum=..., saddr=internal_flow.dip, daddr=internal_flow.sip),
                 tcpudp(src_port=internal_flow.dp, dst_port=internal_flow.sp)])
    else:
        pass
else: # packet from the internal network
    pass
