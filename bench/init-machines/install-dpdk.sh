#!/bin/bash
# See http://dpdk.org/doc/quick-start

# DPDK release to install
DPDK_RELEASE='17.11'

if [ "$RTE_SDK" = '' ]; then
  export RTE_SDK="$HOME/dpdk"
fi

# Check if it's already installed; we manually create a file with the version
if [ ! -f "$RTE_SDK/.version" ] || [ "$(cat "$RTE_SDK/.version")" != "$DPDK_RELEASE" ]; then
    echo "[init] DPDK not found or obsolete, installing..."

    # Install required packages
    sudo apt-get install -yqq wget build-essential linux-headers-`uname -r`

    # If the directory already exists, assume it's an older version, delete it
    if [ -d "$RTE_SDK" ]; then
        rm -rf "$RTE_SDK"
    fi

    # Download DPDK
    wget -O dpdk.tar.xz "https://fast.dpdk.org/rel/dpdk-$DPDK_RELEASE.tar.xz"
    tar xf dpdk.tar.xz
    mv "dpdk-$DPDK_RELEASE" "$RTE_SDK"
    rm dpdk.tar.xz

    # Compile it
    pushd "$RTE_SDK" >> /dev/null
      make install -j$(nproc) T=x86_64-native-linuxapp-gcc DESTDIR=.

      # Write out the version for next run
      echo "$DPDK_RELEASE" > .version
    popd >> /dev/null
fi

