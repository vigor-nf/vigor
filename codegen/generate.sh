#!/bin/bash

FILE_PATH=$1
CODEGENDIR=$(cd $(dirname "${BASH_SOURCE[0]}") && pwd)

set -euo pipefail

function swap()
{
    local TMPFILE=tmp.$$
    mv "$1" $TMPFILE && mv "$2" "$1" && mv $TMPFILE $2
}

pushd $CODEGENDIR
  ocamlbuild -pkg cil main.byte
popd

PREPROC_FILE_PATH=$FILE_PATH.preproc.c
gcc -DCODEGEN -E $FILE_PATH -I $CODEGENDIR/.. > $PREPROC_FILE_PATH
swap $FILE_PATH $PREPROC_FILE_PATH
$CODEGENDIR/_build/main.byte $FILE_PATH
swap $FILE_PATH $PREPROC_FILE_PATH
rm $PREPROC_FILE_PATH
# Check the generated file
verifast -I $CODEGENDIR/.. -I $CODEGENDIR/../lib/stubs/dpdk -c $FILE_PATH.gen.c
