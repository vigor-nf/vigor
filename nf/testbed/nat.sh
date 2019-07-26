sudo apt-get update
KERNEL_VER=$(uname -r | sed 's/-generic//')
sudo apt-get install -y tcpdump git wget build-essential libpcap-dev libglib2.0-dev daemon libnuma-dev python linux-headers-${KERNEL_VER} linux-headers-${KERNEL_VER}-generic

### DPDK
DPDK_RELEASE='17.11'
BUILDDIR=$(pwd)

pushd "$BUILDDIR"
  if [ ! -f dpdk/.version ] || [ "$(cat dpdk/.version)" != "$DPDK_RELEASE" ]; then
    rm -rf dpdk # in case it already exists

    wget -O dpdk.tar.xz "https://fast.dpdk.org/rel/dpdk-$DPDK_RELEASE.tar.xz"
    tar xf dpdk.tar.xz
    rm dpdk.tar.xz
    mv "dpdk-$DPDK_RELEASE" dpdk

    pushd dpdk
      make install -j2 T=x86_64-native-linuxapp-gcc DESTDIR=.

      echo "$DPDK_RELEASE" > .version
    popd
  fi
popd

export RTE_SDK=$BUILDDIR/dpdk
export RTE_TARGET=x86_64-native-linuxapp-gcc

. /nat/testbed/redeploy-nat.sh

daemon -r /nat/testbed/run-nat.sh
