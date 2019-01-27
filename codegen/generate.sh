#!/bin/bash

FILE=$1

set -euo pipefail

function swap()
{
    local TMPFILE=tmp.$$
    mv "$1" $TMPFILE && mv "$2" "$1" && mv $TMPFILE $2
}
PREPROC_FILE=$FILE.preproc.c
ocamlbuild -pkg cil main.byte
gcc -E $FILE > $PREPROC_FILE
swap $FILE $PREPROC_FILE
./_build/main.byte $FILE
swap $FILE $PREPROC_FILE
rm $PREPROC_FILE

echo "Header: "
cat $FILE.gen.h
echo ""
echo "Implementation: "
cat $FILE.gen.c

verifast -c $FILE.gen.c
