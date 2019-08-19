#!/bin/bash
# Removes the temporary files produced by variaous builds in the setup.sh
# also cleans up the apt cache, as we already installed all the packages
# necessary

set -euxo pipefail

# Delete sources used to build our toolchain from scratch
rm -rf binutils gcc

# We don't need tests and tmp files
# And definitely no SVN or GIT
# Most of the object files are redundant as well (but not all)
find . -name .svn | xargs rm -rf
find . -name .git | xargs rm -rf
find llvm -name test | xargs rm -r
find llvm -name unittests | xargs rm -r
find . -name '*.tmp' -delete
find llvm/lib/Target llvm/tools/clang -name '*.inc' -delete
find klee -name '*.a' -delete
find klee -name '*.o' -delete
find klee-uclibc klee-uclibc-binary -name '*.o' -delete
find fastclick fastclick-batch -name '*.o' -delete
find z3 -name '*.o' -delete
find dpdk libmoon/deps/dpdk -name app | xargs rm -rf

# Clean the apt cache
sudo apt-get clean autoclean
sudo apt-get autoremove --yes
sudo rm -rf /var/lib/apt/lists/*
