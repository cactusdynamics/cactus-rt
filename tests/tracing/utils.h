#ifndef CACTUS_RT_TESTS_TRACING_UTILS_H_
#define CACTUS_RT_TESTS_TRACING_UTILS_H_

#include <chrono>

#include "cactus_rt/utils.h"

void WasteTime(std::chrono::microseconds duration) {
  const auto start = cactus_rt::NowNs();
  auto       duration_ns = duration.count() * 1000;
  while (cactus_rt::NowNs() - start < duration_ns) {
  }
}

#endif
