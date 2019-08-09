#!/bin/bash
# $1: "no-verify" to only install compile/runtime dependencies, or no argument to install everything

# Bash "strict mode"
set -euxo pipefail


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
  echo "We recommend you to run the script from the parent directory like this: . $VNDSDIR/setup.sh"
  read -p "Continue installing into $BUILDDIR? [y/n]" -n 1 -r
  echo # move to a new line
  if [[ ! $REPLY =~ ^[Yy]$ ]]; then
    [[ "$0" = "$BASH_SOURCE" ]] && exit 1 || return 1 # handle exits from shell or function but don't exit interactive shell
  fi
fi


if [ ! -f "$PATHSFILE" ]; then
  echo '# The configuration paths for VNDS dependencies' > "$PATHSFILE"
  echo "export VIGOR_DIR=$BUILDDIR"
  # Source the paths file at login
  echo ". $PATHSFILE" >> "$HOME/.profile"
fi

sudo apt-get update
sudo apt-get install -y ca-certificates software-properties-common patch wget build-essential git


# ====
# DPDK
# ====

sudo apt-get install -y libpcap-dev libnuma-dev

# Install the right headers
if [ "$OS" = 'linux' -o "$OS" = 'docker' ]; then
  KERNEL_VER=$(uname -r | sed 's/-generic//')
  if [ "$OS" = 'docker' ]; then
      echo "Warning: the guest uses the host kernel, so the guest should be able to install headers for the host's kernel..."
  fi

  sudo apt-get install -y "linux-headers-$KERNEL_VER"
  sudo apt-get install -y "linux-headers-${KERNEL_VER}-generic"
fi

DPDK_RELEASE='17.11'
pushd "$BUILDDIR"
  if [ ! -f dpdk/.version ] || [ "$(cat dpdk/.version)" != "$DPDK_RELEASE" ]; then
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

      make install -j T=x86_64-native-linuxapp-gcc DESTDIR=.

      echo "$DPDK_RELEASE" > .version
    popd
  fi
popd



# =====
# OCaml
# =====

sudo apt-get install -y opam m4

# OCaml uses variables in its scripts without defining them first - we're in strict mode!
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

if [ ! -e "$BUILDDIR/fastclick" ]; then
  git clone https://github.com/tbarbette/fastclick "$BUILDDIR/fastclick"
  pushd "$BUILDDIR/fastclick"
    git checkout e77376fef6d982fef59517ddd3f1533b9dffc000
    cp elements/etherswitch/etherswitch.* elements/ethernet/. # more convenient
    # No configure/make here, see the click baselines' Makefile
  popd
fi


# =======
# Libmoon
# =======

# the libmoon readme doesn't mention libtbb2, but libmoon fails without it
sudo apt-get install -y libtbb2 lshw

if [ ! -e "$BUILDDIR/libmoon" ]; then
  git clone https://github.com/libmoon/libmoon "$BUILDDIR/libmoon"
  pushd "$BUILDDIR/libmoon"
    git checkout 0cb0843957a1aa8a3580096eee0f5d7246449c85
    # Don't try to bind interfaces
    sed -i '/bind.interfaces/d' build.sh
    ./build.sh
  popd
fi



# ================
# DSOS build tools
# ================

# Make sure grub doesn't ask stupid questions
sudo DEBIAN_FRONTEND=noninteractive apt-get install -yq qemu-system-x86 build-essential wget bison flex \
  libgmp3-dev libmpc-dev libmpfr-dev texinfo libcloog-isl-dev libisl-0.18-dev gnupg \
  xorriso \
  nasm git grub-pc

DSOS_TARGET=x86_64-elf
BINUTILS_RELEASE="2.26.1"
pushd "$BUILDDIR"
  if [ ! -e binutils-build ]; then
    wget -O gnu-keyring.gpg https://ftp.gnu.org/gnu/gnu-keyring.gpg
    wget -O binutils.tar.gz "https://ftp.gnu.org/gnu/binutils/binutils-$BINUTILS_RELEASE.tar.gz"
    wget -O binutils.tar.gz.sig "https://ftp.gnu.org/gnu/binutils/binutils-$BINUTILS_RELEASE.tar.gz.sig"

    gpg --verify --keyring ./gnu-keyring.gpg binutils.tar.gz.sig binutils.tar.gz

    tar xf binutils.tar.gz
    mv "binutils-$BINUTILS_RELEASE" binutils
    rm binutils.tar.gz binutils.tar.gz.sig

    mkdir binutils-build
    pushd binutils-build
      ../binutils/configure --target=$DSOS_TARGET --prefix="$BUILDDIR/binutils-build" --with-sysroot --disable-nls --disable-werror
      make -j
      make -j install
      echo 'PATH='"$BUILDDIR/binutils-build/bin"':$PATH' >> "$PATHSFILE"
      . "$PATHSFILE"
    popd
  fi
popd

GCC_RELEASE="5.4.0"
pushd "$BUILDDIR"
  if [ ! -e gcc-build ]; then
    wget -O gnu-keyring.gpg https://ftp.gnu.org/gnu/gnu-keyring.gpg
    wget -O gcc.tar.gz "https://ftp.gnu.org/gnu/gcc/gcc-5.4.0/gcc-$GCC_RELEASE.tar.gz"
    wget -O gcc.tar.gz.sig "https://ftp.gnu.org/gnu/gcc/gcc-5.4.0/gcc-$GCC_RELEASE.tar.gz.sig"

    gpg --verify --keyring ./gnu-keyring.gpg gcc.tar.gz.sig gcc.tar.gz

    tar xf gcc.tar.gz
    mv "gcc-$GCC_RELEASE" gcc
    rm gcc.tar.gz gcc.tar.gz.sig

    mkdir gcc-build
    pushd gcc-build
      ../gcc/configure --target=$DSOS_TARGET --prefix="$BUILDDIR/gcc-build" --disable-nls --enable-languages=c --without-headers
      make -j all-gcc
      make -j all-target-libgcc
      make -j install-gcc
      make -j install-target-libgcc
      echo 'PATH='"$BUILDDIR/gcc-build/bin"':$PATH' >> "$PATHSFILE"
      . "$PATHSFILE"
    popd
  fi
popd

if [ ! -e "$BUILDDIR/klee-uclibc-binary" ]; then
  cp -r "$BUILDDIR/klee-uclibc" "$BUILDDIR/klee-uclibc-binary"
  pushd "$BUILDDIR/klee-uclibc-binary"
    ./configure \
       --make-native \
       --with-llvm-config="../llvm/Release/bin/llvm-config" \
       --with-cc="../llvm/Release/bin/clang"

    # Use our minimalistic config
    cp "$VNDSDIR/setup/klee-uclibc.config" '.config'

    make clean
    make -j
  popd
fi



# =====================================================================================================
# End of compile/runtime dependencies
if [ $# -eq 0 ] || [ "$1" != 'no-verif' ]; then



# ==
# Z3
# ==

sudo apt-get install -y python2.7

# for Z3 ML bindings
# Num is required for Big_int
opam install ocamlfind num -y

if [ ! -e "$BUILDDIR/z3" ]; then
  git clone --depth 1 --branch z3-4.5.0 https://github.com/Z3Prover/z3 "$BUILDDIR/z3"
  pushd "$BUILDDIR/z3"
    python scripts/mk_make.py --ml -p "$BUILDDIR/z3/build"
    pushd build
      make -k -j || true
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
    make verifast # should be just "make" but the verifast checks fail due to a non auto lemma
    echo 'PATH='"$BUILDDIR/verifast/bin"':$PATH' >> "$PATHSFILE"
    . "$PATHSFILE"
  popd
fi




# ====
# KLEE
# ====

sudo apt-get install -y bison flex zlib1g-dev libncurses5-dev libcap-dev cmake subversion python2.7

if [ ! -e "$BUILDDIR/llvm" ]; then
  svn co https://llvm.org/svn/llvm-project/llvm/tags/RELEASE_342/final "$BUILDDIR/llvm"
  svn co https://llvm.org/svn/llvm-project/cfe/tags/RELEASE_342/final "$BUILDDIR/llvm/tools/clang"
  svn co https://llvm.org/svn/llvm-project/libcxx/tags/RELEASE_342/final "$BUILDDIR/llvm/projects/libcxx"
  pushd "$BUILDDIR/llvm"
    CXXFLAGS="-D_GLIBCXX_USE_CXX11_ABI=0" ./configure --enable-optimized --disable-assertions --enable-targets=host --with-python='/usr/bin/python2'
    make -j
    echo 'PATH='"$BUILDDIR/llvm/Release/bin"':$PATH' >> "$PATHSFILE"
    . "$PATHSFILE"
  popd
fi

if [ ! -e "$BUILDDIR/klee-uclibc" ]; then
  git clone --depth 1 --branch klee_uclibc_v1.2 https://github.com/klee/klee-uclibc.git "$BUILDDIR/klee-uclibc"
  pushd "$BUILDDIR/klee-uclibc"
    ./configure \
     --make-llvm-lib \
     --with-llvm-config="../llvm/Release/bin/llvm-config" \
     --with-cc="../llvm/Release/bin/clang"

    # Use our minimalistic config
    cp "$VNDSDIR/setup/klee-uclibc.config" '.config'

    make -j
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
      make -j
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

printf '\n\n!!!\nIf you ran this script rather than sourcing it, you must source your profile now (e.g. `. ~/.profile`) to get Vigor tools to work.\n!!!\n\n'
exit 0
