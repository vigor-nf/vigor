#!/bin/bash

NIC_PORT=0
FOLDER_NAME="resLatencyUrouter" #can be Vrouter or Mrouter


cd MoonGen

echo "Cache Hit Test Begin\n"

for i in {1..100..5}
do
	echo "Start test with sleep $i microseconds"

   sudo ./build/MoonGen test/cacheHitTest.lua $NIC_PORT $i >> ../$FOLDER_NAME &
	
	PID=$!
	sleep 10
	sudo kill $PID
	
done



