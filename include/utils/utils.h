#ifndef RT_DEMO_UTILS_UTILS_H_
#define RT_DEMO_UTILS_UTILS_H_

#include <cstdint>
#include <ctime>

namespace rt_demo::utils {
inline int64_t TimespecDiffNanoseconds(const struct timespec& ts1, const struct timespec& ts2) {
  int64_t ts1ns = ts1.tv_sec * 1'000'000'000L + ts1.tv_nsec;
  int64_t ts2ns = ts2.tv_sec * 1'000'000'000L + ts2.tv_nsec;

  return ts1ns - ts2ns;
}
}  // namespace rt_demo::utils

#endif
