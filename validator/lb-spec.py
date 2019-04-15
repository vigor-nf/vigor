EXP_TIME = 10
BACKEND_EXP_TIME = 60
EXT_PORT = 0

if a_packet_received and EXP_TIME <= now:
    flow_emap = emap_expire_all(flow_emap, now - EXP_TIME)
if a_packet_received and BACKEND_EXP_TIME <= now:
    backend_ip_emap = emap_expire_all(backend_ip_emap, now - BACKEND_EXP_TIME)

h3 = pop_header(tcpudp, on_mismatch=([],[]))
h2 = pop_header(ipv4, on_mismatch=([],[]))
h1 = pop_header(ether, on_mismatch=([],[]))

assert a_packet_received
assert ((h1.type & 0x10) == 0x10) # 0x10 -> IPv4
assert h2.npid == 6 or h2.npid == 17 # 6/17 -> TCP/UDP

if received_on_port == EXT_PORT: # Packet from the external network - client
    packet_flow = LoadBalancedFlowc(h2.saddr, h2.daddr, h3.src_port, h3.dst_port, h2.npid)
    alloc_flow_and_process_packet = False;
    if emap_has(flow_emap, packet_flow):
        flow_id = emap_get(flow_emap, packet_flow)
        backend_id = vector_get(flow_id_to_backend_id, flow_id)
        if emap_has_idx(backend_ip_emap, backend_id):
            flow_emap = emap_refreh_idx(flow_emap, emap_get(flow_emap, packet_flow), now)
            backend = vector_get(backends, backend_id)
            return ([backend.nic],
                    [ether(h1, saddr=..., daddr=backend.mac),
                     ipv4(h2, cksum=..., daddr=backend.ip),
                     tcpudp(h3)])
        else:
            flow_emap = emap_erase(flow_emap, packet_flow)
            alloc_flow_and_process_packet = True
    else:
        alloc_flow_and_process_packet = True
    if alloc_flow_and_process_packet:
        if emap_exists_with_cht(backend_ip_emap, cht, _LoadBalancedFlow_hash(packet_flow)):
            bknd = emap_choose_with_cht(backend_ip_emap, cht, _LoadBalancedFlow_hash(packet_flow))
            if not emap_full(flow_emap):
                idx = the_index_allocated
                flow_emap = emap_add(flow_emap, packet_flow, idx, now)
                flow_id_to_backend_id = vector_set(flow_id_to_backend_id, idx, bknd)
            backend = vector_get(backends, bknd)
            return ([backend.nic],
                    [ether(h1, saddr=..., daddr=backend.mac),
                     ipv4(h2, cksum=..., daddr=backend.ip),
                     tcpudp(h3)])
        else:
            return ([],[])
else: # A heartbeat from a backend
    bknd_addr = ip_addrc(h2.saddr)
    if emap_has(backend_ip_emap, bknd_addr):
        backend_ip_emap = emap_refresh_idx(backend_ip_emap, emap_get(backend_ip_emap, bknd_addr), now)
    else:
        if not emap_full(backend_ip_emap):
            idx = the_index_allocated
            backend_ip_emap = emap_add(backend_ip_emap, bknd_addr, idx, now)
            backends = vector_set(backends, idx,
                                  LoadBalancedBackendc(received_on_port, h1.saddr, h2.saddr))
    return ([],[])
