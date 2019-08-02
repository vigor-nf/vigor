
# Test Procedure

## Protocole

1. Generate routes using the RoutesGenerator (pass the number of routes as parameters)

2. copy the lua files to MoonRoute/code/MoonRoute and rename it as "cfg.lua"

3. copy the file without extension to vnds/nf/unverified-router (or vigrouter) and rename it "routes"

4. launch one of the routers and send packets using MoonGen (either the cache miss test or the cache hit test)

5. (OPTIONAL) you can use the file named nf_main_for_test.c (in nf/unverified-router) instead of the default nf_main.c. It allows to send back packet to where they come from (easier test setup)


## Test setup:


S1: routes packets received from S2 back to S2     <=====>    S2: send packets and receive response from the router (calculate latency and throughput)
				
