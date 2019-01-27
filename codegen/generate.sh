#!/bin/bash

FILE=$1

set -euo pipefail
PREPROC_FILE=$FILE.preproc.c
ocamlbuild -pkg cil main.byte
gcc -E $FILE > $PREPROC_FILE
./_build/main.byte $PREPROC_FILE
rm -f $PREPROC_FILE

echo "Header: "
cat $PREPROC_FILE.gen.h
echo ""
echo "Implementation: "
cat $PREPROC_FILE.gen.c
