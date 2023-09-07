#!/bin/bash

set -xe

cd ${CACTUS_RT_BUILD_DIR}
ctest -V
