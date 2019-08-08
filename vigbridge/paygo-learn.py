# SOSPTODO fix this up if needed & then use it in spec.py!!!!

from state import macTable

macTable.expireOlder(now - EXP_TIME)
macTable[pkt.src_mac] = (port, now)
