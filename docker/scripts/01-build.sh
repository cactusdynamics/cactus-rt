#!/bin/bash

set -xe

cmake -B${CACTUS_RT_BUILD_DIR} \
  -DENABLE_CLANG_TIDY=ON \
  -DBUILD_DOCS=ON \
  -DBUILD_TESTING=ON \
  -DENABLE_TRACING=${ENABLE_TRACING:-ON} \
  -DCMAKE_BUILD_TYPE=RelWithDebInfo
cmake --build ${CACTUS_RT_BUILD_DIR} -j $(nproc)
