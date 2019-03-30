
#export RTE_TARGET=x86_64-native-linuxapp-gcc
#export RTE_SDK=/home/hedi/vnds-lpm-router-bachelor/dpdk


echo Compiling the router

sleep 1

make router

echo Starting the router

sleep 1
 ./launch.sh &


sleep 8

echo Starting the packet generator

sleep 3

cd 
cd MoonGen

rm result.txt

sudo ./build/MoonGen test/perf_test.lua 0 >> result.txt & 

sleep 45


echo TEST OVER !


sudo pkill router
sudo pkill MoonGen

