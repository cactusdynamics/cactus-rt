#ifndef CACTUS_RT_DEADLINE_H_
#define CACTUS_RT_DEADLINE_H_

#include <sched.h>
#include <spdlog/spdlog.h>

#include <cerrno>
#include <ctime>

#include "cactus_rt/linux/sched_ext.h"

constexpr size_t kDefaultStackSize = 8 * 1024 * 1024;  // 8MB

// Earliest Deadline First scheduler. More information on this can be found here:
// https://docs.kernel.org/scheduler/sched-deadline.html

namespace cactus_rt {
namespace schedulers {
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
      SPDLOG_ERROR("unable to sched_setattr: {}", std::strerror(errno));
      throw std::runtime_error{"failed to sched_setattr"};
    }
  }

  inline static double Sleep(const struct timespec& /*next_wakeup_time */) noexcept {
    // Ignoring error as man page says "In the Linux implementation, sched_yield() always succeeds."
    sched_yield();
    return 0.0;
  }
};
}  // namespace schedulers

// Deadline needs access to the cyclic thread's period
// This template specialization avoids needing to pass the thread into a Deadline::SetThreadScheduling by
// manually overriding the period of Deadline::Config in the template-specialized constructor. User setting of sched_period directly on the Deadline::Config object for cyclic threads is
// not supported.
template <>
inline CyclicThread<schedulers::Deadline>::CyclicThread(const std::string&                  name,
                                                        int64_t                             period_ns,
                                                        const schedulers::Deadline::Config& config,
                                                        std::vector<size_t>                 cpu_affinity,
                                                        size_t                              stack_size)
    : Thread<schedulers::Deadline>(name, config, cpu_affinity, stack_size),
      period_ns_(period_ns),
      scheduler_config_(config) {
  scheduler_config_.sched_period_ns = static_cast<uint64_t>(period_ns);
}

}  // namespace cactus_rt
#endif