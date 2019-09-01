from state import backends, backend_ip_emap
BACKEND_EXP_TIME = 3600000000 * 1000
EXT_PORT = 2

if a_packet_received:
    backend_ip_emap.expire_all(now - BACKEND_EXP_TIME)

h3 = pop_header(tcpudp, on_mismatch=([],[]))
h2 = pop_header(ipv4, on_mismatch=([],[]))
h1 = pop_header(ether, on_mismatch=([],[]))

bknd_addr = ip_addrc(h2.saddr)
if (received_on_port != EXT_PORT and # A heartbeat from a backend
    not backend_ip_emap.has(bknd_addr) and
    not backend_ip_emap.full()):
    idx = the_index_allocated
    backend_ip_emap.add(bknd_addr, idx, now)
    backends.set(idx, LoadBalancedBackendc(received_on_port, h1.saddr, h2.saddr))
else:
    pass
