#ifndef CACTUS_RT_OTHER_H_
#define CACTUS_RT_OTHER_H_

#include <errno.h>
#include <sched.h>
#include <spdlog/spdlog.h>
#include <time.h>

#include "cactus_rt/linux/sched_ext.h"

namespace cactus_rt {
namespace schedulers {
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
      SPDLOG_ERROR("unable to sched_setattr: {}", std::strerror(errno));
      throw std::runtime_error{"failed to sched_setattr"};
    }
  }

  // Kind of meaningless for SCHED_OTHER because there's no RT guarantees
  inline static double Sleep(const struct timespec& next_wakeup_time) noexcept {
    // TODO: check for errors?
    // TODO: can there be remainders?
    clock_nanosleep(CLOCK_MONOTONIC, TIMER_ABSTIME, &next_wakeup_time, NULL);
    return 0.0;
  }
};
}  // namespace schedulers
}  // namespace cactus_rt
#endif