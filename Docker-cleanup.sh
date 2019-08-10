#!/bin/bash
# Removes the temporary files produced by variaous builds in the setup.sh
# also cleans up the apt cache, as we already installed all the packages
# necessary

set -euxo pipefail

# Delete sources used to build our toolchain from scratch
rm -rf binutils gcc

# We don't need tests and tmp files
# And definitely no SVN
find . -name .svn | xargs rm -rf
find llvm -name test | xargs rm -r
find llvm -name unittests | xargs rm -r
find . -name '*.tmp' -delete
find llvm/lib/Target -name '*.inc' -delete
find llvm/tools/clang -name '*.inc' -delete
find klee -name '*.a' -delete
find klee -name '*.o' -delete

# Remove temporary build files
#find . -name '*.o' -delete
#find . -name '*.d' -delete

# Clean the apt cache
sudo apt-get clean autoclean
sudo apt-get autoremove --yes
sudo rm -rf /var/lib/apt/lists/*
