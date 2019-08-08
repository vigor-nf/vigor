from state import dyn_emap, stat_emap, dyn_vals
EXP_TIME = 10 * 1000

h = pop_header(ether, on_mismatch=([],[]))

dyn_emap.expire_all(now - EXP_TIME)

if dyn_emap.has(h.saddr):
    dyn_emap.refresh_idx(dyn_emap.get(h.saddr), now)
else:
    if not dyn_emap.full():
        idx = the_index_allocated
        dyn_emap.add(h.saddr, idx, now)
        dyn_vals.set(idx, DynamicValuec(received_on_port))

static_key = StaticKeyc(h.daddr, received_on_port)
if stat_emap.has(static_key):
    output_port = stat_emap.get(static_key)
    if output_port == -2 or output_port == received_on_port:
        return ([],[])
    else:
        return ([output_port], [ether(h)])
else:
    if dyn_emap.has(h.daddr):
        idx = dyn_emap.get(h.daddr)
        forward_to = dyn_vals.get(idx)
        if (forward_to.output_port == received_on_port):
            return ([],[])
        else:
            return ([forward_to.output_port], [ether(h)])
    else:
        return ([1-received_on_port], [ether(h)]) # broadcast, TODO: generalize

