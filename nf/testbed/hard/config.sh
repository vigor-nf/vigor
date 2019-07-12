# --------- #
# Middlebox #
# --------- #

# These values must always be set
MB_HOST=icnalsp3s2.epfl.ch
MB_PCI_INTERNAL=0000:83:00.1
MB_PCI_EXTERNAL=0000:83:00.0

# These values are only useful if you benchmark non-DPDK NFs
MB_DEVICE_INTERNAL=p802p2
MB_DEVICE_EXTERNAL=p802p1
MB_IP_INTERNAL=192.168.6.2
MB_IP_EXTERNAL=192.168.4.2
MB_IPS_BACKENDS="192.168.4.3 192.168.4.4 192.168.4.5 192.168.4.6"


# ------ #
# Tester #
# ------ #

# These values must always be set
TESTER_HOST=icnalsp3s1.epfl.ch
TESTER_PCI_INTERNAL=0000:83:00.1
TESTER_PCI_EXTERNAL=0000:83:00.0

# These values are only useful if you benchmark non-DPDK NFs
TESTER_MAC_INTERNAL=90:e2:ba:55:12:25
TESTER_MAC_EXTERNAL=90:e2:ba:55:12:24
TESTER_IP_INTERNAL=192.168.6.5
TESTER_IP_EXTERNAL=192.168.4.10


# ----- #
# Other #
# ----- #

# Do not change unless Linux or DPDK change!
KERN_NIC_DRIVER=ixgbe
DPDK_NIC_DRIVER=igb_uio
