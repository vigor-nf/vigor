#!/bin/bash

pushd $HOME >> /dev/null
  if [ ! -f moon-gen/.built ]; then
      git clone --depth=1 git://github.com/emmericp/MoonGen.git moon-gen

      cd moon-gen
      ./build.sh
      printf '\n\n!!!\nErrors from driver binding failures are normal.\n!!!\n\n'
      touch .built
  fi
popd >> /dev/null
