#ifndef CACTUS_TRACING_UTILS_H_
#define CACTUS_TRACING_UTILS_H_

#include <cstdint>
#include <ctime>

namespace cactus_tracing {

inline uint64_t NowNs(clockid_t clock_id = CLOCK_MONOTONIC) {
  struct timespec ts;
  clock_gettime(clock_id, &ts);
  return static_cast<uint64_t>(ts.tv_sec) * 1'000'000'000 + static_cast<uint64_t>(ts.tv_nsec);
}

}  // namespace cactus_tracing

#endif
