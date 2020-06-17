from state import stat_emap
h = pop_header(ether, on_mismatch=([],[]))
static_key = StaticKeyc(h.daddr, received_on_port)
if stat_emap.has(static_key) and (stat_emap.get(static_key) == -2):
    return ([],[])
