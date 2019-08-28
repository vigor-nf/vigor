#!/bin/bash

FILE_PATH=$1
CODEGENDIR=$(cd $(dirname "${BASH_SOURCE[0]}") && pwd)

set -euo pipefail

cp $FILE_PATH $CODEGENDIR/nf_data_spec.ml

pushd $CODEGENDIR > /dev/null
  corebuild loop_boilerplate_gen.byte > /dev/null
popd > /dev/null

rm $CODEGENDIR/nf_data_spec.ml

$CODEGENDIR/_build/loop_boilerplate_gen.byte
