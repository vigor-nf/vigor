#!/bin/bash

# Configuration file mapping real hosts, addresses and ports
# to abstract names used in the scripts.

# Subnets

EXTERNAL_SUBNET=192.168.2.0
SERVER_SUBNET=192.168.200.0

# Middlebox

MB_HOST=icnalsp3s2.epfl.ch

MB_INTERNAL_MAC=00:1e:67:92:29:6d
MB_EXTERNAL_MAC=00:1e:67:92:29:6c
MB_TO_SRV_MAC=00:1e:67:92:29:6e

MB_IP_INTERNAL=192.168.3.2
MB_IP_EXTERNAL=192.168.2.2
MB_IP_TO_SRV=192.168.200.2

MB_DEVICE_INTERNAL=em3
MB_DEVICE_EXTERNAL=em2
MB_DEVICE_TO_SRV=em4

MB_PCI_INTERNAL='0000:02:00.2'
MB_PCI_EXTERNAL='0000:02:00.1'
MB_PCI_TO_SRV='0000:02:00.3'

# Tester

TESTER_HOST=icnalsp3s1.epfl.ch

TESTER_DEVICE_INTERNAL=em3
TESTER_DEVICE_EXTERNAL=em2

TESTER_PCI_INTERNAL=0000:02:00.2
TESTER_PCI_EXTERNAL=0000:02:00.1

TESTER_MAC_INTERNAL=00:1e:67:92:2a:bd
TESTER_MAC_EXTERNAL=00:1e:67:92:2a:bc

TESTER_IP_INTERNAL=192.168.3.5
TESTER_IP_EXTERNAL=192.168.2.10
TESTER_IP_FOR_STUB=192.168.200.5

# Server

SERVER_HOST=icnalsp3s3.epfl.ch

SERVER_IP=192.168.200.10
SERVER_MAC=00:1e:67:92:2a:2b
SERVER_DEVICE=em4

# Other

NAT_SRC_PATH=$HOME/vnds/nat
STUB_SRC_PATH=$HOME/vnb-nat
