#!/bin/bash
cmake -B${CACTUS_RT_BUILD_DIR} -DENABLE_CLANG_TIDY=ON
cmake --build ${CACTUS_RT_BUILD_DIR} -j $(nproc)
