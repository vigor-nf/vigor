h = pop_header(ether, on_mismatch=([],[]))
return ([1 - received_on_port],
        [ether(h, saddr=..., daddr=...)])
