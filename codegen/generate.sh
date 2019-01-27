#!/bin/bash
FILE=$1
PREPROC_FILE=$FILE.preproc.c
ocamlbuild -pkg cil main.byte
gcc -E $FILE > $PREPROC_FILE
./_build/main.byte $PREPROC_FILE
rm -f $PREPROC_FILE
