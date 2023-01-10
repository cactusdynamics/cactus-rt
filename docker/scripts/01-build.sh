#!/bin/bash
cmake -B${CACTUS_RT_BUILD_DIR} -DENABLE_CLANG_TIDY=ON -DBUILD_DOCS=ON
cmake --build ${CACTUS_RT_BUILD_DIR} -j $(nproc)
