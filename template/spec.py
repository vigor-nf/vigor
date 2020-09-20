# ===
# This is your NF's spec
# ===

# ===
# Import state if needed like this:
# from state import flow_emap
# ===


# ===
# You can declare constants
# ===
SOME_VALUE = 42

# ===
# You can also use the non-container values from the state as-is:
# ===
assert example_value == 42

# ===
# Variable 'a_packet_received' is true if a packet was received, false otherwise
# ===
if not a_packet_received:
  # ===
  # Return a tuple of lists:
  # 1. The list of devices the packet must be forwarded to;
  # 2. The headers the forwarded packet must have.
  # ===
  return ([],[])

# ===
# Get input packet headers in reverse order, they are a stack.
# The on_mismatch argument has the same semantics as a return; if the input packet did not have this header, it will return that value
# ===
h3 = pop_header(tcpudp, on_mismatch=([],[]))
h2 = pop_header(ipv4, on_mismatch=([],[]))
h1 = pop_header(ether, on_mismatch=([],[]))

# ===
# You can write assertions
# ===
assert h2.npid == 6 or h2.npid == 17 # 6/17 -> TCP/UDP

# ===
# You can use standard Python if/else
# ===
if 1 == 2:
  assert false

# ===
# Variable 'received_on_port' contains the port on which the input packet was received
# ===
# ... (Python's ellipsis) indicates the framework to ignore the corresponding field.
# i.e. if you do not want to specify ether.saddr value, because it is set by the L2, you can
# "skip" when specifying the ethernet header with
# ether(h1, saddr=...) - this will enforce the same ethernet header as h1,
# but with an arbitrary saddr
return ([1 - received_on_port],
        [ether(h1, saddr=..., daddr=...),
         ipv4(h2, cksum=..., saddr=..., daddr=...),
         tcpudp(src_port=..., dst_port=...)])
