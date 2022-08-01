#ifndef RT_DEMO_RT_UTILS_H_
#define RT_DEMO_RT_UTILS_H_

#include <cstdint>
#include <ctime>

namespace cactus_rt {
inline int64_t NowNs() {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec * 1'000'000'000 + ts.tv_nsec;
}

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
