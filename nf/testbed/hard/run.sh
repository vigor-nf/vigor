#!/bin/bash
. ./config.sh

# Master script to run the prepared benchmarks for VigNAT-related programs.
# Can benchmark different implementations, including non-NATs,
# using different scenarios.

# Parameters:
# $1: The app, either a known name or a DPDK NAT-like app.
#     Known names: "netfilter".
#     Otherwise, a folder name containing a DPDK NAT-like app, e.g. "~/vnds/nat"
# $2: The scenario, one of the following:
#     "mg-1p": Measure throughput: find the rate at which the middlebox
#              starts losing 1% of packets.
#     "mg-existing-flows-latency": Measure the forwarding latency for existing
#                                  flows.
#     "mg-new-flows-latency": Measure the forwarding latency for new flows.
#     "loopback": Measure throughput.
#                 Tester and middlebox are connected together in a loop,
#                 using 2 interfaces on each, in different subnets; server is ignored.
#     "1p": Measure throughput.
#           Find the point at which the middlebox starts dropping 1% of packets.
#     "passthrough": Measure latency.
#                    Tester sends packets to server, which pass through the middlebox;
#                    all machines are in the same subnet.
#     "rr": Measure latency.
#           Tester sends packets to server, which are modified by the middlebox;
#           there are two subnets, tester-middlebox and middlebox-server.
#           a.k.a. request/response
# $3: Results file

MIDDLEBOX=$1
SCENARIO=$2
NF_TYPE=$3
RESULTS_FILE=$4

if [ -z $MIDDLEBOX ]; then
    echo "[run] No middlebox specified" 1>&2
    exit 1
fi

if [ -z $SCENARIO ]; then
    echo "[run] No scenario specified" 1>&2
    exit 2
fi

if [ -z $RESULTS_FILE ]; then
    echo "[bench] No results file specified" 1>&2
    exit 3
fi

if [ -f "$RESULTS_FILE" ]; then
    echo "[run] results file exists! exiting" 1>&2
    exit 4
fi


case $SCENARIO in
    "mg-1p")

        case $NF_TYPE in
	    "NAT"|"FW"|"NOP")	
        	LUA_SCRIPT="l4-load-find-1p.lua"
	        ;;

     	    "LB")
                LUA_SCRIPT="l3-lb-load-find-1p.lua"
                ;;
     	    
	    "Pol")
                LUA_SCRIPT="l3-load-find-1p.lua"
                ;;
            
     	    "Br")
                LUA_SCRIPT="l2-load-find-1p.lua"
                ;;
            
            *)
	     	echo "[bench] Unknown NF_TYPE: $NF_TYPE" 1>&2
		exit 10
   		;;
        esac

        echo "[bench] Benchmarking throughput..."
	ssh $TESTER_HOST "sudo ~/moon-gen/build/MoonGen ~/scripts/moongen/$LUA_SCRIPT -r 5000 -u 5 -t 20 1 0"
        scp $TESTER_HOST:mf-find-mg-1p.txt "./$RESULTS_FILE"
        ssh $TESTER_HOST "sudo rm mf-find-mg-1p.txt"
        ;;

    "mg-new-flows-latency")
        
	case $NF_TYPE in
	    "Pol")	
        	LUA_SCRIPT="l3-latency-light.lua"
	        ;;

     	    "FW"|"NAT"|"NOP")
                LUA_SCRIPT="l4-latency-light.lua"
                ;;
     	   
       	    "LB")
                LUA_SCRIPT="l3-lb-latency-light.lua"
                ;;
            
     	    "Br")
                LUA_SCRIPT="l2-latency-light.lua"
                ;;
            
            *)
	     	echo "[bench] Unknown NF_TYPE: $NF_TYPE" 1>&2
		exit 10
   		;;
        esac

        echo "[bench] Benchmarking latency..."
        ssh $TESTER_HOST "sudo ~/moon-gen/build/MoonGen ~/scripts/moongen/$LUA_SCRIPT -r 1000 -u 5 -t 2 1 0"
        scp $TESTER_HOST:mf-lat.txt "./$RESULTS_FILE"
        ssh $TESTER_HOST "sudo rm mf-lat.txt"
        ;;

    "mg-existing-flows-latency")
        LUA_SCRIPT="l3-latency-light.lua"
        echo "[bench] Benchmarking latency..."
        ssh $TESTER_HOST "sudo ~/moon-gen/build/MoonGen ~/scripts/moongen/$LUA_SCRIPT -r 100 -u 5 -t 20 1 0"
        scp $TESTER_HOST:mf-lat.txt "./$RESULTS_FILE"
        ssh $TESTER_HOST "sudo rm mf-lat.txt"
        ;;

    "loopback"|"1p")
        LUA_SCRIPT="regular-with-bin-mf.lua"
        if [ $SCENARIO = "1p" ]; then
            LUA_SCRIPT="find-breaking-point-mf.lua"
        fi

        echo "[bench] Benchmarking throughput..."
        ssh $TESTER_HOST "bash ~/scripts/pktgen/run.sh ~/scripts/pktgen/$LUA_SCRIPT"
        scp $TESTER_HOST:pktgen/multi-flows.txt "./$RESULTS_FILE"
        ssh $TESTER_HOST "rm pktgen/multi-flows.txt"
        ;;

    "rr"|"passthrough")
        # No difference from a benchmarking point of view, only setup varies

        echo "[bench] Benchmarking latency..."
        ssh $TESTER_HOST "bash ~/scripts/bench/latency.sh ~/bench.results"
        scp $TESTER_HOST:bench.results "./$RESULTS_FILE"
        ssh $TESTER_HOST "rm ~/bench.results"
        ;;

    *)
        echo "[bench] Unknown scenario: $MIDDLEBOX" 1>&2
        exit 10
        ;;
esac
