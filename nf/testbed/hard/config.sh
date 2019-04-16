
# Config for 10G:
# [mb]{p801p1 (90:e2:ba:55:12:5c)} -- {p801p1 ()}[server]
# [mb]{p802p2 (90:e2:ba:55:14:11)/dev6} -- {p802p2 (90:e2:ba:55:12:25)/dev8}[tester]
# [mb]{p802p1 (90:e2:ba:55:14:10)/dev5} -- {p802p1 (90:e2:ba:55:12:24)/dev7}[tester]

# direct link tester:
# p802p2 90:e2:ba:55:12:25 -- p801p1 90:e2:ba:55:14:38

KERN_NIC_DRIVER=ixgbe
DPDK_NIC_DRIVER=igb_uio

# Subnets

EXTERNAL_SUBNET=192.168.4.0

# Middlebox

MB_HOST=icnalsp3s3.epfl.ch

MB_MAC_INTERNAL=90:e2:ba:55:14:64
MB_MAC_EXTERNAL=90:e2:ba:55:14:65

MB_IP_INTERNAL=192.168.6.2
MB_IP_EXTERNAL=192.168.4.2

MB_DEVICE_INTERNAL=p786p1
MB_DEVICE_EXTERNAL=p786p2

MB_PCI_INTERNAL=0000:06:00.0
MB_PCI_EXTERNAL=0000:06:00.1


# Tester

TESTER_HOST=matteo@icnalsp3s4.epfl.ch

TESTER_DEVICE_INTERNAL=enp6s0f0
TESTER_DEVICE_EXTERNAL=enp6s0f1

TESTER_PCI_INTERNAL=0000:06:00.0
TESTER_PCI_EXTERNAL=0000:06:00.1

TESTER_MAC_INTERNAL=90:e2:ba:55:15:5c
TESTER_MAC_EXTERNAL=90:e2:ba:55:15:5d

TESTER_IP_INTERNAL=192.168.6.5
TESTER_IP_EXTERNAL=192.168.4.10

# Other

CASE_ROOT="$( cd "$( dirname "${BASH_SOURCE[0]}")"/../../../../  >/dev/null && pwd )"

# Fix the case root folder for the tester, where it should be just home
if [ "${CASE_ROOT##/home/}" == "${CASE_ROOT}" ]; then
  CASE_ROOT=$HOME
fi

export RTE_SDK=$CASE_ROOT/dpdk
export RTE_TARGET=x86_64-native-linuxapp-gcc
