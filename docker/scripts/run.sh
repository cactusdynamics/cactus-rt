#!/bin/bash

export CACTUS_RT_SOURCE_DIR=/cactus-rt/source
export CACTUS_RT_BUILD_DIR=/cactus-rt/build

set -xe

cd $CACTUS_RT_SOURCE_DIR
/cactus-rt/scripts/00-format.sh
/cactus-rt/scripts/01-build.sh
/cactus-rt/scripts/02-test.sh
