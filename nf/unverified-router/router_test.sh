
#path to where the test script for the router is located
ROUTER_PATH="/home/hedi/Documents/EPFL/yee/vnds/nf/unverified-router"

#path to a MoonGen installation
MOONGEN_PATH="/home/hedi/Documents/EPFL/bachelor_project/MoonGen"


#path to MoonRoute
MOONROUTE_PATH="."


cd $ROUTER_PATH

make router

#compile the routes generator
javac RoutesGenerator.java



#generate routes and launch tests for the unverified router
for i in `seq 0 1000 100000`; do
	
	cd $ROUTER_PATH

	rm routes

	java RoutesGenerator $i
	
	mv Routes${i} routes

	mv Routes${i}.lua $MOONROUTE_PATH
	
	echo "Starting the router"

	sleep 1
 	./launch.sh &

	sleep 8

	echo Starting the packet generator

	sleep 3

	cd $MOONGEN_PATH
	
	sudo ./build/MoonGen test/perf_test.lua 0 >> "Routes${i}result" & 

done


#launch test for moonroute



#launch test for the verified router



















