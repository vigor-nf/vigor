#!/bin/bash

make router

sudo ./build/router --vdev=net_tap2,iface=router,mac=fixed --file-prefix pref_router

