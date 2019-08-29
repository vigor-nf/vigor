from state import lpm
h2 = pop_header(ipv4, on_mismatch=([],[]))
h1 = pop_header(ether, on_mismatch=([],[]))
# Malformed IPv4
if (h2.vihl & 15) < 5 or packet_size - 14 < (((h2.len & 0xFF) << 8) | ((h2.len & 0xFF00) >> 8)):
    return ([],[])
port = lpm.lookup(h2.daddr)
if port == received_on_port: return ([],[])
return ([port], [ether(h1, saddr=..., daddr=...), ipv4(h2)])
