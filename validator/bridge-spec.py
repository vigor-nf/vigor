EXP_TIME = 10

h = pop_header(ether, on_mismatch=([],[]))

if EXP_TIME <= now:
    dyn_emap = emap_expire_all(dyn_emap, now - EXP_TIME)

if emap_has(dyn_emap, h.saddr):
    dyn_emap = emap_refresh_idx(dyn_emap, emap_get(dyn_emap, h.saddr), now)
else:
    if not emap_full(dyn_emap):
        idx = the_index_allocated
        dyn_emap = emap_add(dyn_emap, h.saddr, idx, now)
        dyn_vals = vector_set(dyn_vals, idx, DynamicValuec(received_on_port))

static_key = StaticKeyc(h.daddr, received_on_port)
if emap_has(stat_emap, static_key):
    output_port = emap_get(stat_emap, static_key)
    if output_port == -2 or output_port == received_on_port:
        return ([],[])
    else:
        return ([output_port], [ether(h)])
else:
    if emap_has(dyn_emap, h.daddr):
        idx = emap_get(dyn_emap, h.daddr)
        forward_to = vector_get(dyn_vals, idx)
        if (forward_to.output_port == received_on_port):
            return ([],[])
        else:
            return ([forward_to.output_port], [ether(h)])
    else:
        return ([1-received_on_port], [ether(h)]) # broadcast, TODO: generalize

