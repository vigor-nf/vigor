#!/bin/bash

VNDSDIR=$(cd $(dirname "${BASH_SOURCE[0]}") && pwd)
BUILDDIR=`pwd`
PATHSFILE="$BUILDDIR/paths.sh"

# Bash "strict mode"
set -euxo pipefail

sudo apt update
sudo apt -y install qemu-system-x86 build-essential wget bison flex \
  libgmp3-dev libmpc-dev libmpfr-dev texinfo libcloog-isl-dev libisl-dev gnupg \
  nasm git grub

DSOS_TARGET=x86_64-elf

# Binutils
BINUTILS_RELEASE="2.26.1"

pushd "$BUILDDIR"
  if [ ! -f binutils-build/.version ] || [ "$(cat binutils-build/.version)" != "$BINUTILS_RELEASE" ]; then
    rm -rf binutils-build binutils

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
      make -j`nproc`
      make -j`nproc` install
      echo 'PATH='"$BUILDDIR/binutils-build/bin"':$PATH' >> "$PATHSFILE"
      echo "$BINUTILS_RELEASE" > .version
      . "$PATHSFILE"
    popd
  fi
popd

# GCC
GCC_RELEASE="5.4.0"

pushd "$BUILDDIR"
  if [ ! -f gcc-build/.version ] || [ "$(cat gcc-build/.version)" != "$GCC_RELEASE" ]; then
    rm -rf gcc-build gcc

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
      make -j`nproc` all-gcc
      make -j`nproc` all-target-libgcc
      make -j`nproc` install-gcc
      make -j`nproc` install-target-libgcc
      echo 'PATH='"$BUILDDIR/gcc-build/bin"':$PATH' >> "$PATHSFILE"
      echo "$GCC_RELEASE" > .version
      . "$PATHSFILE"
    popd
  fi
popd
