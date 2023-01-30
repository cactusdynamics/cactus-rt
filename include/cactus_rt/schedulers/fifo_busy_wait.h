#ifndef CACTUS_RT_FIFO_BUSY_WAIT_H_
#define CACTUS_RT_FIFO_BUSY_WAIT_H_

#include <sched.h>
#include <spdlog/spdlog.h>

#include <cerrno>
#include <ctime>

#include "../linux/sched_ext.h"
#include "../utils.h"

namespace cactus_rt::schedulers {
/**
 * @brief This is a special FIFO scheduler that will busy sleep to maintain a
 * jitter-free loop rate at the cost of CPU. This value can be determined from
 * cyclictest.
 *
 * In Madden 2019 ("Challenges Using Linux as a Real-Time Operating System"),
 * the author suggested a method of maintaining very strict timing for periodic
 * callbacks with the FIFO scheduler. The way it works is as follows:
 *
 * 1. Before running/programming the application, measure the hardware +
 * scheduling latency of the system you're deploying to.
 * 2. In the loop, instead of sleeping to the next desired wake up time, sleep
 * until the next desired wake up time minus the estimated hardware + scheduling
 * latency.
 * 3. Once the application wakes up, the code should be slightly ahead of
 * schedule. Thus, you busy wait until the original desired wake up time.
 *
 * This is explained in details at [this * link](https://shuhaowu.com/blog/2022/04-linux-rt-appdev-part4.html#trick-to-deal-with-wake-up-jitter).
 * Specifically, one should look at Figure 3 for a detailed schematic on what
 * happens.
 */
class FifoBusyWait {
 public:
  struct Config {
    uint32_t priority = 80;

    /**
     * @brief An estimate of the hardware + scheduling latency. This estimate
     * should be greater than the actual hardware + scheduling latency to ensure
     * the Loop() function will not be called late.
     */
    int32_t scheduling_latency_estimate_ns = 150'000;
  };

  // This code should really be the same as the Fifo code.
  // TODO: figure out a way to reuse that code? Maybe it's not necessary, tho.
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
      SPDLOG_ERROR("unable to sched_setattr: {}", std::strerror(errno));
      throw std::runtime_error{"failed to sched_setattr"};
    }
  }

  inline static double Sleep(const struct timespec& next_wakeup_time, const Config& config) noexcept {
    // TODO: refactor some of these timespec -> ns int64_t conversion into an utils function
    int64_t next_wakeup_time_ns = next_wakeup_time.tv_sec * 1'000'000'000 + next_wakeup_time.tv_nsec;
    int64_t now = NowNs();

    // In Madden 2019 ("Challenges Using Linux as a Real-Time Operating System"),
    // the author suggested that busy wait should occur if the time to next wake
    // up is less than 2 x scheduling latency. The reason cited is because if the
    // present task goes to sleep, it may take up to 1 x scheduling latency to
    // schedule another task, and another 1 x scheduling latency to schedule the
    // present task, making it pointless.
    //
    // Perhaps my understanding is bad, but I'm not sure how to measure the
    // above defined scheduling latency. I would just take the max latency number
    // from cyclictest instead, which I think is appropriate for just 1x.
    if (next_wakeup_time_ns - now >= config.scheduling_latency_estimate_ns) {
      struct timespec next_wakeup_time_minus_scheduling_latency = AddTimespecByNs(next_wakeup_time, -config.scheduling_latency_estimate_ns);
      clock_nanosleep(CLOCK_MONOTONIC, TIMER_ABSTIME, &next_wakeup_time_minus_scheduling_latency, nullptr);
    }

    now = NowNs();

    while (next_wakeup_time_ns - NowNs() > 0) {
      // busy wait
      // TODO: add asm nop? Doesn't seem necessary as we're running a bunch of clock_gettime syscalls anyway..
    }

    return static_cast<double>(NowNs() - now);
  }
};
}  // namespace cactus_rt::schedulers
#endif
