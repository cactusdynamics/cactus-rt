#ifndef CACTUS_RT_DEADLINE_H_
#define CACTUS_RT_DEADLINE_H_

#include <sched.h>

#include <cerrno>
#include <cstring>
#include <ctime>
#include <iostream>
#include <stdexcept>
#include <vector>

#include "../linux/sched_ext.h"

// Earliest Deadline First scheduler. More information on this can be found here:
// https://docs.kernel.org/scheduler/sched-deadline.html

namespace cactus_rt::schedulers {
class Deadline {
 public:
  struct Config {
    Config(uint64_t runtime_ns, uint64_t deadline_ns)
        : sched_runtime_ns(runtime_ns),
          sched_deadline_ns(deadline_ns) {}
    uint64_t sched_runtime_ns;
    uint64_t sched_deadline_ns;
    uint64_t sched_period_ns = 0;  // User setting of sched_period for cyclic threads is not supported.
  };

  inline static void SetThreadScheduling(const Config& config) {
    // Self scheduling attributes
    sched_attr attr = {};
    attr.size = sizeof(attr);
    attr.sched_flags = 0;
    attr.sched_nice = 0;
    attr.sched_priority = 0;

    attr.sched_policy = SCHED_DEADLINE;  // Set the scheduler policy
    attr.sched_runtime = config.sched_runtime_ns;
    attr.sched_deadline = config.sched_deadline_ns;
    attr.sched_period = config.sched_period_ns;

    auto ret = sched_setattr(0, &attr, 0);
    if (ret < 0) {
      throw std::runtime_error{std::string("failed to sched_setattr: ") + std::strerror(errno)};
    }

    std::cout << "Set deadline schedulinng\n";
  }

  inline static int64_t Sleep(const struct timespec& /*next_wakeup_time */) noexcept {
    // Ignoring error as man page says "In the Linux implementation, sched_yield() always succeeds."
    sched_yield();
    return 0;
  }
};
}  // namespace cactus_rt::schedulers
#endif
