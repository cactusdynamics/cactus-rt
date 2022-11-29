#!/bin/bash

clang-format --version && find . \( -iname '*.h' -o -iname '*.cc' -o -iname '*.c' -o -iname '*.hpp' -o -iname '*.cpp' \) -not \( -path './build/*' -prune \) -not \( -path './external/*' -prune \) | xargs clang-format --dry-run -Werror
