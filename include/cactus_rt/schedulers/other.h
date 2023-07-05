#ifndef CACTUS_RT_OTHER_H_
#define CACTUS_RT_OTHER_H_

#include <sched.h>

#include <cerrno>
#include <cstring>
#include <ctime>
#include <stdexcept>

#include "../linux/sched_ext.h"

namespace cactus_rt::schedulers {
class Other {
 public:
  struct Config {
    int32_t nice = 0;
  };

  inline static void SetThreadScheduling(const Config& config) {
    // Self scheduling attributes
    sched_attr attr = {};
    attr.size = sizeof(attr);
    attr.sched_flags = 0;
    attr.sched_nice = config.nice;    // Set the thread niceness
    attr.sched_policy = SCHED_OTHER;  // Set the scheduler policy

    auto ret = sched_setattr(0, &attr, 0);
    if (ret < 0) {
      throw std::runtime_error{std::string("failed to sched_setattr: ") + std::strerror(errno)};
    }
  }

  // Kind of meaningless for SCHED_OTHER because there's no RT guarantees
  inline static int64_t Sleep(const struct timespec& next_wakeup_time) noexcept {
    // TODO: check for errors?
    // TODO: can there be remainders?
    clock_nanosleep(CLOCK_MONOTONIC, TIMER_ABSTIME, &next_wakeup_time, nullptr);
    return 0;
  }
};
}  // namespace cactus_rt::schedulers
#endif
