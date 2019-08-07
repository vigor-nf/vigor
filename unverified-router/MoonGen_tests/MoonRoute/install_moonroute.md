
# How to install MoonRoute


## Configuration

server: kernel version 3.14
gcc version 4.8.5
need lua 5.1 and luasocket

## Installation

[Download MoonRoute here](https://github.com/emmericp/MoonRoute-data)

Go into /code/MoonGen

Edit CMakeCache.txt and replace every occurance of "/home/rainer/ma/MoonGen" (hardcoded path..) by your own path

run sudo ./build.sh

make

The MoonGen executable should be there.


## Binding the NICs

Bind the Nic using the modules provided in MoonRoute/code/MoonGen/deps/dpdk/x86_64-native-linuxapp-gcc/kmod with the following commands:

cd  MoonRoute/code/MoonGen/deps/dpdk/x86_64-native-linuxapp-gcc/kmod

sudo modprobe uio

sudo insmod igb_uio.ko


## how to run the router

Simply run ./MoonGen  ../MoonRoute/router.lua

The maximum number of entries can be modified in rte_lpm.h found in MoonGen/deps/dpdk ...


