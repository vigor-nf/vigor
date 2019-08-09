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
