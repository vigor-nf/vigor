
echo Starting the router

 ./launch.sh &

ROUTER_PID=$!

echo Router will be shut down !


sudo kill $ROUTER_PID
