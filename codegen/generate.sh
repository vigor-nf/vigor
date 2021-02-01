#!/bin/bash

CODEGENDIR=$(cd $(dirname "${BASH_SOURCE[0]}") && pwd)
set -euo pipefail

function swap()
{
  local TMPFILE=tmp.$$
  mv "$1" $TMPFILE && mv "$2" "$1" && mv $TMPFILE $2
}

# enable backtraces
export OCAMLRUNPARAM=b

pushd $CODEGENDIR > /dev/null
  ocamlbuild -tag debug -pkg cil main.byte > /dev/null
popd > /dev/null

for FILE_PATH in $@; do
  PREPROC_FILE_PATH=$FILE_PATH.preproc.c
  gcc -E $FILE_PATH -I $CODEGENDIR/.. -I $CODEGENDIR/../libvig/models/dpdk > $PREPROC_FILE_PATH
  swap $FILE_PATH $PREPROC_FILE_PATH
  $CODEGENDIR/_build/main.byte $FILE_PATH
  swap $FILE_PATH $PREPROC_FILE_PATH
  rm $PREPROC_FILE_PATH
  # Check the generated file if possible
  if command -v verifast >/dev/null 2>&1 ; then
    if ! verifast -I $CODEGENDIR/.. -I $CODEGENDIR/../libvig/models/dpdk -c $FILE_PATH.gen.c > /dev/null; then
      echo 'Oh no! The generated code does not verify!'
      exit 1
    fi
  fi
done
