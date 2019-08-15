import table_updates
h = pop_header(ether, on_mismatch=([],[]))
static_key = StaticKeyc(h.daddr, received_on_port)
if stat_emap.has(static_key):
    if (stat_emap.get(static_key) == -2 or stat_emap.get(static_key) == received_on_port):
        return ([],[])
elif dyn_emap.has(h.daddr) and dyn_vals.get(dyn_emap.get(h.daddr)) == DynamicValuec(received_on_port):
    return ([],[])
else:
    return ([...],[ether(h)])
