import table_updates
h = pop_header(ether, on_mismatch=([],[]))
static_key = StaticKeyc(h.daddr, received_on_port)
if not stat_emap.has(static_key) and not dyn_emap.has(h.daddr):
    return ([1-received_on_port], [ether(h)]) # broadcast, TODO: generalize
