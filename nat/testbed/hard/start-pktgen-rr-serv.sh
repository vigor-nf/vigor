cd ~/pktgen && fifo=$(mktemp -u) && mkfifo "$fifo" && (rm "$fifo" && { sudo ./app/app//x86_64-native-linuxapp-gcc/pktgen -c 0x1f -n 3 -- -P -m "[1-2:3-4].0" -f ../scripts/pktgen-scripts/provision-rr.lua -G < /dev/fd/1 3&>1 > ./pktgen-log.txt <&3 3<&-; } &) 3<> "$fifo" | :