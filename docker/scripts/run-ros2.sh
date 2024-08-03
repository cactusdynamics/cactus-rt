#!/bin/bash

export WORKSPACE_DIR=/workspace

set -xe

cd $WORKSPACE_DIR
colcon build --cmake-args "-DENABLE_CLANG_TIDY=ON"
