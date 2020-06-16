LAN_DEVICE = 1
WAN_DEVICE = 0

h2 = pop_header(rte_ipv4, on_mismatch=([],[]))
# Malformed IPv4
if (h2.vihl & 15) < 5 or packet_size - 14 < (((h2.len & 0xFF) << 8) | ((h2.len & 0xFF00) >> 8)):
    return ([],[])
h1 = pop_header(rte_ether, on_mismatch=([],[]))

if received_on_port == LAN_DEVICE:
    return ([WAN_DEVICE],[rte_ether(h1), rte_ipv4(h2)])
else:
    pass
