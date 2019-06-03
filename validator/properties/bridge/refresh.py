from state import dyn_emap
EXP_TIME = 10
h = pop_header(ether, on_mismatch=([],[]))
if EXP_TIME <= now:
    dyn_emap.expire_all(now - EXP_TIME)
if dyn_emap.has(h.saddr):
    dyn_emap.refresh_idx(dyn_emap.get(h.saddr), now)
else:
    pass
