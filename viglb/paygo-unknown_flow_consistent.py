from state import flow_emap, backends, backend_ip_emap, cht
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
if (received_on_port == EXT_PORT and
    not flow_emap.has(packet_flow) and
    backend_ip_emap.exists_with_cht(cht, _LoadBalancedFlow_hash(packet_flow))):
    bknd = backend_ip_emap.choose_with_cht(cht, _LoadBalancedFlow_hash(packet_flow))
    backend = backends.get(bknd)
    return ([backend.nic],
            [ether(h1, saddr=..., daddr=backend.mac),
             ipv4(h2, cksum=..., daddr=backend.ip),
             tcpudp(h3)])
    pass # This allows us to ignore the state changes
else:
    pass
