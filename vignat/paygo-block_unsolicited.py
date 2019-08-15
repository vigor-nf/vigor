from state import flow_emap
EXP_TIME = 10 * 1000
EXT_PORT = 1

if a_packet_received:
    flow_emap.expire_all(now - EXP_TIME)

h3 = pop_header(tcpudp, on_mismatch=([],[]))
h2 = pop_header(ipv4, on_mismatch=([],[]))
h1 = pop_header(ether, on_mismatch=([],[]))
flow_indx = h3.dst_port - start_port
if received_on_port == EXT_PORT and not flow_emap.has_idx(flow_indx):
    return ([],[])
else:
    pass
