# --------- #
# Middlebox #
# --------- #

# These values must always be set
export MB_CPU=8 # the index of the CPU on which the middlebox will run
export MB_HOST=icnalsp3s2.epfl.ch
export MB_PCI_INTERNAL=0000:83:00.1
export MB_PCI_EXTERNAL=0000:83:00.0

# These values are only useful if you benchmark non-DPDK NFs
export MB_DEVICE_INTERNAL=p802p2
export MB_DEVICE_EXTERNAL=p802p1
export MB_IP_INTERNAL=192.168.6.2
export MB_IP_EXTERNAL=192.168.4.2
export MB_IPS_BACKENDS="192.168.4.3 192.168.4.4 192.168.4.5 192.168.4.6"


# ------ #
# Tester #
# ------ #

# These values must always be set
export TESTER_HOST=icnalsp3s1.epfl.ch
export TESTER_PCI_INTERNAL=0000:83:00.1
export TESTER_PCI_EXTERNAL=0000:83:00.0

# These values are only useful if you benchmark non-DPDK NFs
export TESTER_MAC_INTERNAL=90:e2:ba:55:12:25
export TESTER_MAC_EXTERNAL=90:e2:ba:55:12:24
export TESTER_IP_INTERNAL=192.168.6.5
export TESTER_IP_EXTERNAL=192.168.4.10


# ----- #
# Other #
# ----- #

# Do not change unless Linux or DPDK change!
export KERN_NIC_DRIVER=ixgbe
export DPDK_NIC_DRIVER=igb_uio

# Change only if you know what you're doing (e.g. you installed DPDK to a different path than home)
export RTE_SDK=$HOME/dpdk
export RTE_TARGET=x86_64-native-linuxapp-gcc
