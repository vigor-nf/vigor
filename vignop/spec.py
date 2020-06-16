h = pop_header(rte_ether, on_mismatch=([],[]))
return ([1 - received_on_port],
        [rte_ether(h, saddr=..., daddr=...)])
