EXP_TIME = 10
EXT_IP_ADDR = ext_ip
EXT_PORT = 1

flow_emap = emap(initial_fm, initial_fv, initial_heap)
final_flow_emap = emap(final_flow_map, final_flow_vec, final_flow_chain)

if EXP_TIME < now: # consider only normal moments, remote from the start of the epoch
    if a_packet_received: # This is probably implied by the first pop_header call, TODO: check
        flow_emap = emap_expire_all(flow_emap, now - EXP_TIME)

        h1 = pop_header(ether, on_mismatch=([],[]))
        h2 = pop_header(ipv4, on_mismatch=([],[]))
        h3 = pop_header(tcp_udp, on_mismatch=([],[]))

        # TODO: VVV replace this with assertions, as we already expect the ether/ip/tcpudp stack
        # because of the above 3 calls to pop_header
        if ((h1.type & 0x10) == 0x10): # 0x10 -> IPv4
            if (h2.inpid == 6 or h2.inpid == 17): # 6/17 -> TCP/UDP
                if (received_on_port == EXT_PORT):
                    flow_indx = h3.idst_port - start_port
                    if (emap_has_idx(flow_emap, flow_indx)): # Flow is present in the table
                        internal_flow = emap_get_key(flow_emap, flow_indx)
                        flow_emap = emap_refresh_idx(flow_emap, flow_indx, now)
                        if (internal_flow.sp != h2.isaddr or
                            internal_flow.dp != h2.isrc_port or
                            internal_flow.prot != h2.inpid):
                            return ([],[])
                        else:
                            return ([internal_flow.idev],
                                    [ether(h1, saddr=..., daddr=...),
                                     ipv4(h2, icksum=..., saddr=internal_flow.dip, daddr=internal_flow.sip),
                                     tcpudp(src_port=internal_flow.dp, dst_port=internal_flow.sp)])
                    else:
                        return ([],[])
                else: # packet from the internal network
                    internal_flow_id = FlowId(isrc_port, idst_port, isaddr, idaddr, received_on_port, inpid)
                    if (emap_has(flow_emap, internal_flow_id)): # flow present in the table
                        idx = emap_get(flow_emap, internal_flow_id)
                        flow_emap = emap_refresh_idx(flow_emap, idx, now)
                        return ([EXT_PORT],
                                [ether(h1, saddr=..., daddr=...),
                                 ipv4(h2, icksum=..., saddr=EXT_IP_ADDR),
                                 tcpudp(h3, src_port=idx + start_port)])
                    else: # No flow in the table
                        if (emap_full(flow_emap)): # flowtable overflow
                            return ([],[])
                        else:
                            idx = the_index_allocated
                            flow_emap = emap_add(flow_emap, internal_flow_id, idx, now)
                            return ([EXT_PORT],
                                    [ether(h1, saddr=..., daddr=...),
                                     ipv4(h2, icksum=..., saddr=EXT_IP_ADDR, daddr=internal_flow_id.sip),
                                     tcpudp(h3, src_port=idx + start_port)])
            else: # Non TCP or UDP packet
                return ([],[])
        else: # Non IPv4 packet
            return ([],[])
