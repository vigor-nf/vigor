LAN_DEVICE = 0
WAN_DEVICE = 1
WORD_SIZE = 4
ETHER_IP_HDRLEN = 34

h2 = pop_header(ipv4, on_mismatch=([],[]))
# malformed ipv4 header
if h2.vihl & 0xf < 5 or (packet_size - ETHER_IP_HDRLEN < ((h2.vihl & 0xf) - 5)*WORD_SIZE):
    return ([],[])
h1 = pop_header(ether, on_mismatch=([],[]))

if received_on_port == LAN_DEVICE:
    return ([WAN_DEVICE],[ether(h1), ipv4(h2)])
else:
    pass
