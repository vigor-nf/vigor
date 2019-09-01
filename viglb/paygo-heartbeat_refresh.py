from state import backend_ip_emap
BACKEND_EXP_TIME = 3600000000 * 1000
EXT_PORT = 2

if a_packet_received:
    backend_ip_emap.expire_all(now - BACKEND_EXP_TIME)

h3 = pop_header(tcpudp, on_mismatch=([],[]))
h2 = pop_header(ipv4, on_mismatch=([],[]))
h1 = pop_header(ether, on_mismatch=([],[]))

bknd_addr = ip_addrc(h2.saddr)
if received_on_port != EXT_PORT and backend_ip_emap.has(bknd_addr):
    backend_ip_emap.refresh_idx(backend_ip_emap.get(bknd_addr), now)
else:
    pass
