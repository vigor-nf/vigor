#!/bin/bash

FILE_PATH=$1
CODEGENDIR=$(cd $(dirname "${BASH_SOURCE[0]}") && pwd)

set -euo pipefail

cp $FILE_PATH $CODEGENDIR/nf_data_spec.ml

pushd $CODEGENDIR
  ocamlbuild loop_boilerplate_gen.byte
popd

$CODEGENDIR/_build/loop_boilerplate_gen.byte
