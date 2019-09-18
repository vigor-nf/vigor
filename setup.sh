#!/bin/bash
# $1: "no-verify" to only install compile/runtime dependencies,
#     or no argument to install everything

# Bash "strict mode"
set -euo pipefail


# =====
# Setup
# =====

VNDSDIR=$(cd $(dirname "${BASH_SOURCE[0]}") && pwd)
BUILDDIR=`pwd`
PATHSFILE="$BUILDDIR/paths.sh"


OS='linux'
if grep docker /proc/1/cgroup -qa; then OS='docker'; fi


if [ "$BUILDDIR" -ef "$VNDSDIR" ] && [ "$OS" != "docker" ]; then
  echo 'It is not recommented to install the dependencies into the project root directory.'
  echo "We recommend you to run the script from the parent directory like this:"
  echo ". $VNDSDIR/setup.sh"
  read -p "Continue installing into $BUILDDIR? [y/n]" -n 1 -r
  echo # move to a new line
  if [[ ! $REPLY =~ ^[Yy]$ ]]; then
    # handle exits from shell or function but don't exit interactive shell
    [[ "$0" = "$BASH_SOURCE" ]] && exit 1 || return 1
  fi
fi


if [ ! -f "$PATHSFILE" ]; then
  echo '# The configuration paths for VNDS dependencies' > "$PATHSFILE"
  echo "export VIGOR_DIR=$BUILDDIR" >> "$PATHSFILE"
  # Source the paths file at login
  echo ". $PATHSFILE" >> "$HOME/.profile"
fi

sudo apt-get update
sudo apt-get install -y ca-certificates software-properties-common \
                        patch wget build-essential git cloc


# ====
# DPDK
# ====

sudo apt-get install -y libpcap-dev libnuma-dev

# Install the right headers
if [ "$OS" = 'linux' -o "$OS" = 'docker' ]; then
  KERNEL_VER=$(uname -r | sed 's/-generic//')
  if [ "$OS" = 'docker' ]; then
      echo "Warning: the guest uses the host kernel,"
      echo " so the guest should be able to install headers for the host's kernel..."
  fi

  sudo apt-get install -y "linux-headers-$KERNEL_VER"
  sudo apt-get install -y "linux-headers-${KERNEL_VER}-generic"
fi

DPDK_RELEASE='17.11'
pushd "$BUILDDIR"
  if [ ! -f dpdk/.version ] || \
     [ "$(cat dpdk/.version)" != "$DPDK_RELEASE" ]; then
    rm -rf dpdk # in case it already exists

    wget -O dpdk.tar.xz "https://fast.dpdk.org/rel/dpdk-$DPDK_RELEASE.tar.xz"
    tar xf dpdk.tar.xz
    rm dpdk.tar.xz
    mv "dpdk-$DPDK_RELEASE" dpdk

    echo 'export RTE_TARGET=x86_64-native-linuxapp-gcc' >> "$PATHSFILE"
    echo "export RTE_SDK=$BUILDDIR/dpdk" >> "$PATHSFILE"
    . "$PATHSFILE"

    pushd dpdk
      # Apply the Vigor patches
      for p in "$VNDSDIR/setup/"dpdk.*.patch; do
        patch -p1 < "$p"
      done

      make install -j$(nproc) T=x86_64-native-linuxapp-gcc DESTDIR=.

      echo "$DPDK_RELEASE" > .version
    popd
  fi
popd



# =====
# OCaml
# =====

sudo apt-get install -y opam m4

# OCaml uses variables in its scripts without
# defining them first - we're in strict mode!
if [ -z ${PERL5LIB+x} ]; then
  export PERL5LIB=''
fi
if [ -z ${MANPATH+x} ]; then
  export MANPATH=''
fi

opam init -y
opam switch 4.06.0

if ! grep -q opam "$PATHSFILE"; then
  echo 'PATH='"$HOME/.opam/system/bin"':$PATH' >> "$PATHSFILE"
  echo ". $HOME/.opam/opam-init/init.sh" >> "$PATHSFILE"
  . "$PATHSFILE"
fi

# Codegenerator dependencies
opam install goblint-cil -y



# ======
# Python
# ======

sudo apt-get install -y python3.6



# =========
# FastClick
# =========

sudo apt-get install -y libz-dev

# We make two folders,
# one configured with batching and the other without,
# because it's a configure-time thing and rebuilding it takes a long time
if [ ! -e "$BUILDDIR/fastclick" ]; then
  git clone https://github.com/tbarbette/fastclick "$BUILDDIR/fastclick"
  pushd "$BUILDDIR/fastclick"
    git checkout e77376fef6d982fef59517ddd3f1533b9dffc000
    cp elements/etherswitch/etherswitch.* elements/ethernet/. # more convenient
  popd
  cp -r "$BUILDDIR/fastclick" "$BUILDDIR/fastclick-batch"
  for dir in "$BUILDDIR/fastclick" "$BUILDDIR/fastclick-batch"; do
    pushd "$dir"
      if [ "$dir" = "$BUILDDIR/fastclick" ]; then
        CLICK_BATCH_PARAM=--disable-batch
      else
        CLICK_BATCH_PARAM=--enable-auto-batch
      fi
      # most likely some of those flags are redundant with the defaults, oh well
      CFLAGS="-O3" CXXFLAGS="-std=gnu++11 -O3" \
            ./configure --quiet --enable-multithread \
                        --disable-linuxmodule --enable-intel-cpu \
                        --enable-user-multithread \
                        --disable-dynamic-linking --enable-poll \
                        --enable-bound-port-transfer --enable-dpdk \
                        --with-netmap=no --enable-zerocopy \
                        --disable-dpdk-pool --disable-dpdk-packet \
                        $CLICK_BATCH_PARAM
      make -j$(nproc)
    popd
  done
fi



# =======
# Libmoon
# =======

# the libmoon readme doesn't mention libtbb2, but libmoon fails without it
sudo apt-get install -y libtbb2 lshw cmake

if [ ! -e "$BUILDDIR/libmoon" ]; then
  git clone https://github.com/libmoon/libmoon "$BUILDDIR/libmoon"
  pushd "$BUILDDIR/libmoon"
    git checkout 0cb0843957a1aa8a3580096eee0f5d7246449c85
    # Don't try to bind interfaces
    sed -i '/bind.interfaces/d' build.sh
    # Don't set --lcores, we set it ourselves
    sed -i '/--lcores=/d' lua/dpdk.lua
    ./build.sh
  popd
fi



# ================
# NFOS build tools
# ================

# Make sure grub doesn't ask stupid questions
sudo DEBIAN_FRONTEND=noninteractive \
     apt-get install -yq qemu-system-x86 build-essential wget bison flex \
                         libgmp3-dev libmpc-dev libmpfr-dev texinfo \
                         libcloog-isl-dev libisl-0.18-dev gnupg \
                         xorriso nasm git grub-pc

NFOS_TARGET=x86_64-elf
BINUTILS_RELEASE="2.26.1"
pushd "$BUILDDIR"
  if [ ! -e binutils-build ]; then
    wget -O gnu-keyring.gpg https://ftp.gnu.org/gnu/gnu-keyring.gpg
    wget -O binutils.tar.gz \
         "https://ftp.gnu.org/gnu/binutils/binutils-$BINUTILS_RELEASE.tar.gz"
    wget -O binutils.tar.gz.sig \
         "https://ftp.gnu.org/gnu/binutils/binutils-$BINUTILS_RELEASE.tar.gz.sig"

    gpg --verify --keyring ./gnu-keyring.gpg binutils.tar.gz.sig binutils.tar.gz

    tar xf binutils.tar.gz
    mv "binutils-$BINUTILS_RELEASE" binutils
    rm binutils.tar.gz binutils.tar.gz.sig

    mkdir binutils-build
    pushd binutils-build
      ../binutils/configure --target=$NFOS_TARGET \
                            --prefix="$BUILDDIR/binutils-build" --with-sysroot \
                            --disable-nls --disable-werror
      make -j$(nproc)
      make -j$(nproc) install
      echo 'PATH='"$BUILDDIR/binutils-build/bin"':$PATH' >> "$PATHSFILE"
      . "$PATHSFILE"
    popd
  fi
popd

GCC_RELEASE="5.4.0"
pushd "$BUILDDIR"
  if [ ! -e gcc-build ]; then
    wget -O gnu-keyring.gpg https://ftp.gnu.org/gnu/gnu-keyring.gpg
    wget -O gcc.tar.gz \
         "https://ftp.gnu.org/gnu/gcc/gcc-5.4.0/gcc-$GCC_RELEASE.tar.gz"
    wget -O gcc.tar.gz.sig \
         "https://ftp.gnu.org/gnu/gcc/gcc-5.4.0/gcc-$GCC_RELEASE.tar.gz.sig"

    gpg --verify --keyring ./gnu-keyring.gpg gcc.tar.gz.sig gcc.tar.gz

    tar xf gcc.tar.gz
    mv "gcc-$GCC_RELEASE" gcc
    rm gcc.tar.gz gcc.tar.gz.sig

    mkdir gcc-build
    pushd gcc-build
      ../gcc/configure --target=$NFOS_TARGET --prefix="$BUILDDIR/gcc-build" \
                       --disable-nls --enable-languages=c --without-headers
      make -j$(nproc) all-gcc
      make -j$(nproc) all-target-libgcc
      make -j$(nproc) install-gcc
      make -j$(nproc) install-target-libgcc
      make clean
      echo 'PATH='"$BUILDDIR/gcc-build/bin"':$PATH' >> "$PATHSFILE"
      . "$PATHSFILE"
    popd
  fi
popd

# LLVM required to build klee-uclibc
# (including the libc necessary to build NFOS)
sudo apt-get install -y bison flex zlib1g-dev libncurses5-dev \
                        libcap-dev subversion python2.7

if [ ! -e "$BUILDDIR/llvm" ]; then
  svn co https://llvm.org/svn/llvm-project/llvm/tags/RELEASE_342/final "$BUILDDIR/llvm"
  svn co https://llvm.org/svn/llvm-project/cfe/tags/RELEASE_342/final "$BUILDDIR/llvm/tools/clang"
  svn co https://llvm.org/svn/llvm-project/libcxx/tags/RELEASE_342/final "$BUILDDIR/llvm/projects/libcxx"
  pushd "$BUILDDIR/llvm"
    CXXFLAGS="-D_GLIBCXX_USE_CXX11_ABI=0" \
        ./configure --enable-optimized --disable-assertions \
                    --enable-targets=host --with-python='/usr/bin/python2'
    make -j$(nproc)
    echo 'PATH='"$BUILDDIR/llvm/Release/bin"':$PATH' >> "$PATHSFILE"
    . "$PATHSFILE"
  popd
fi

# micro libC for producing the NFOS standalone OS images

if [ ! -e "$BUILDDIR/klee-uclibc-binary" ]; then
  git clone --depth 1 --branch klee_uclibc_v1.2 \
            https://github.com/klee/klee-uclibc.git "$BUILDDIR/klee-uclibc-binary"
  pushd "$BUILDDIR/klee-uclibc-binary"
    ./configure \
       --make-native \
       --with-llvm-config="../llvm/Release/bin/llvm-config" \
       --with-cc="../llvm/Release/bin/clang"

    # Use our minimalistic config
    cp "$VNDSDIR/setup/klee-uclibc.config" '.config'

    make clean
    make -j$(nproc)
  popd
fi



# ==============================================================================
# End of compile/runtime dependencies
if [ $# -eq 0 ] || [ "$1" != 'no-verify' ]; then



# ==
# Z3
# ==

sudo apt-get install -y python2.7

# for Z3 ML bindings
# Num is required for Big_int
opam install ocamlfind num -y

if [ ! -e "$BUILDDIR/z3" ]; then
  git clone --depth 1 --branch z3-4.5.0 \
            https://github.com/Z3Prover/z3 "$BUILDDIR/z3"
  pushd "$BUILDDIR/z3"
    python scripts/mk_make.py --ml -p "$BUILDDIR/z3/build"
    pushd build
      make -k -j$(nproc) || true
      # -jN here may break the make (hidden deps or something)
      make
      make install

      # Weird, but required sometimes
      # Remove the outdated libz3.so
      sudo apt-get remove  libz3-dev || true
      sudo rm -f /usr/lib/x86_64-linux-gnu/libz3.so || true
      sudo rm -f /usr/lib/x86_64-linux-gnu/libz3.so.4 || true
      sudo rm -f /usr/lib/libz3.so || true
      # Install the new libz3.so
      sudo ln -fs "$BUILDDIR/z3/build/libz3.so" "/usr/lib/libz3.so"
      sudo ldconfig
      # Install it in .opam as well, VeriFast wants it there...
      ln -fs /usr/lib/libz3.so ~/.opam/4.06.0/.
    popd
  popd
fi



# ========
# VeriFast
# ========

# inspired from VeriFast's readme
sudo apt-get install -y --no-install-recommends \
                     ocaml-native-compilers camlp4 unzip libgtk2.0-dev \
                     valac gtksourceview2.0-dev \
                     liblablgtk2-ocaml-dev liblablgtksourceview2-ocaml-dev
# Not mentioned by VeriFast's readme, required anyway
opam install ocamlfind camlp4 -y
# VFIDE dependency
opam install lablgtk -y

if [ ! -e "$BUILDDIR/verifast" ]; then
  git clone --depth 1 https://github.com/vigor-nf/verifast "$BUILDDIR/verifast"
  pushd "$BUILDDIR/verifast/src"
    make verifast # should be just "make",
                  # but the verifast checks fail due to a non auto lemma
    echo 'PATH='"$BUILDDIR/verifast/bin"':$PATH' >> "$PATHSFILE"
    . "$PATHSFILE"
  popd
fi




# ====
# KLEE
# ====

if [ ! -e "$BUILDDIR/klee-uclibc" ]; then
  git clone --depth 1 --branch klee_uclibc_v1.2 \
            https://github.com/klee/klee-uclibc.git "$BUILDDIR/klee-uclibc"
  pushd "$BUILDDIR/klee-uclibc"
    ./configure \
     --make-llvm-lib \
     --with-llvm-config="../llvm/Release/bin/llvm-config" \
     --with-cc="../llvm/Release/bin/clang"

    # Use our minimalistic config
    cp "$VNDSDIR/setup/klee-uclibc.config" '.config'

    make -j$(nproc)
  popd
fi

if [ ! -e "$BUILDDIR/klee" ]; then
  git clone --depth 1 https://github.com/vigor-nf/klee.git "$BUILDDIR/klee"
  pushd "$BUILDDIR/klee"
    rm -rf build
    mkdir build
    pushd build
      CXXFLAGS="-D_GLIBCXX_USE_CXX11_ABI=0" \
      CMAKE_PREFIX_PATH="$BUILDDIR/z3/build" \
      CMAKE_INCLUDE_PATH="$BUILDDIR/z3/build/include/" \
       cmake \
       -DENABLE_UNIT_TESTS=OFF \
       -DBUILD_SHARED_LIBS=OFF \
       -DENABLE_KLEE_ASSERTS=ON \
       -DLLVM_CONFIG_BINARY="$BUILDDIR/llvm/Release/bin/llvm-config" \
       -DLLVMCC="$BUILDDIR/llvm/Release/bin/clang" \
       -DLLVMCXX="$BUILDDIR/llvm/Release/bin/clang++" \
       -DENABLE_SOLVER_Z3=ON \
       -DENABLE_KLEE_UCLIBC=ON \
       -DKLEE_UCLIBC_PATH="$BUILDDIR/klee-uclibc" \
       -DENABLE_POSIX_RUNTIME=ON \
       ..
      make -j$(nproc)
      echo 'PATH='"$BUILDDIR/klee/build/bin"':$PATH' >> "$PATHSFILE"
      echo "export KLEE_INCLUDE=$BUILDDIR/klee/include" >> "$PATHSFILE"
      echo "export KLEE_BUILD_PATH=$BUILDDIR/klee/build" >> "$PATHSFILE"
      . "$PATHSFILE"
    popd
  popd
fi



# =====
# Vigor
# =====

sudo apt-get install -y time parallel bc

# Validator dependencies
opam install ocamlfind core sexplib menhir -y



# end of the if that checked for no-verif
fi

printf '\n\n!!!\nIf you ran this script rather than sourcing it,'
printf ' you must source your profile now (e.g. `. ~/.profile`)'
printf ' to get Vigor tools to work.\n!!!\n\n'
