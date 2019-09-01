from state import flow_emap, flow_id_to_backend_id, backends, backend_ip_emap
EXP_TIME = 10 * 1000
BACKEND_EXP_TIME = 3600000000 * 1000
EXT_PORT = 2

if a_packet_received:
    flow_emap.expire_all(now - EXP_TIME)
    backend_ip_emap.expire_all(now - BACKEND_EXP_TIME)

h3 = pop_header(tcpudp, on_mismatch=([],[]))
h2 = pop_header(ipv4, on_mismatch=([],[]))
h1 = pop_header(ether, on_mismatch=([],[]))

packet_flow = LoadBalancedFlowc(h2.saddr, h2.daddr, h3.src_port, h3.dst_port, h2.npid)
if received_on_port == EXT_PORT and flow_emap.has(packet_flow):
    flow_id = flow_emap.get(packet_flow)
    backend_id = flow_id_to_backend_id.get(flow_id)
    if backend_ip_emap.has_idx(backend_id):
        flow_emap.refresh_idx(flow_emap.get(packet_flow), now)
        backend = backends.get(backend_id)
        return ([backend.nic],
                [ether(h1, saddr=..., daddr=backend.mac),
                 ipv4(h2, cksum=..., daddr=backend.ip),
                 tcpudp(h3)])
    else:
        pass
else:
    pass
