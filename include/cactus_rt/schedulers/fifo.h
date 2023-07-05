#ifndef CACTUS_RT_FIFO_H_
#define CACTUS_RT_FIFO_H_

#include <sched.h>

#include <cerrno>
#include <cstring>
#include <ctime>
#include <stdexcept>

#include "../linux/sched_ext.h"

namespace cactus_rt::schedulers {
class Fifo {
 public:
  struct Config {
    uint32_t priority = 80;
  };

  inline static void SetThreadScheduling(const Config& config) {
    // Self scheduling attributes
    sched_attr attr = {};
    attr.size = sizeof(attr);
    attr.sched_flags = 0;
    attr.sched_nice = 0;
    attr.sched_priority = config.priority;  // Set the scheduler priority
    attr.sched_policy = SCHED_FIFO;         // Set the scheduler policy

    auto ret = sched_setattr(0, &attr, 0);
    if (ret < 0) {
      throw std::runtime_error{std::string("failed to sched_setattr: ") + std::strerror(errno)};
    }
  }

  inline static int64_t Sleep(const struct timespec& next_wakeup_time) noexcept {
    // TODO: check for errors?
    // TODO: can there be remainders?
    clock_nanosleep(CLOCK_MONOTONIC, TIMER_ABSTIME, &next_wakeup_time, nullptr);
    return 0;
  }
};
}  // namespace cactus_rt::schedulers
#endif
