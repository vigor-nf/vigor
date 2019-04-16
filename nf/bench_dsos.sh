#!/bin/bash

qemu-system-x86_64 -enable-kvm -cpu host -m 1G -curses -device vfio-pci,host=81:00.0 -device vfio-pci,host=81:00.1 -cdrom dsos-x86_64.iso &
