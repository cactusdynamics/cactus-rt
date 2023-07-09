#ifndef CACTUS_RT_UTILS_H_
#define CACTUS_RT_UTILS_H_

#include <cstdint>
#include <ctime>

namespace cactus_rt {

/**
 * @brief Get the current nanosecond in monotonic clock (not wall clock!)
 *
 * @return the current nanosecond in monotonic clock
 */
inline int64_t NowNs() {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec * 1'000'000'000 + ts.tv_nsec;
}

/**
 * @brief Get the current nano second in wall clock
 *
 * @return the current nano second in wall clock
 */
inline int64_t WallNowNs() {
  struct timespec ts;
  clock_gettime(CLOCK_REALTIME, &ts);
  return ts.tv_sec * 1'000'000'000 + ts.tv_nsec;
}

inline struct timespec AddTimespecByNs(struct timespec ts, int64_t ns) {
  ts.tv_nsec += ns;

  while (ts.tv_nsec >= 1'000'000'000) {
    ++ts.tv_sec;
    ts.tv_nsec -= 1'000'000'000;
  }

  while (ts.tv_nsec < 0) {
    --ts.tv_sec;
    ts.tv_nsec += 1'000'000'000;
  }

  return ts;
}

}  // namespace cactus_rt

#endif
