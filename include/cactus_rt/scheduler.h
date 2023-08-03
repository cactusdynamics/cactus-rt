#ifndef CACTUS_RT_SCHEDULER_H_
#define CACTUS_RT_SCHEDULER_H_

#include <sched.h>

#include <cstring>
#include <ctime>
#include <stdexcept>

#include "cactus_rt/linux/sched_ext.h"

namespace cactus_rt {
class Scheduler {
 public:
  virtual ~Scheduler() = default;

  virtual void SetSchedAttr() const = 0;

  virtual void Sleep(struct timespec next_wakeup_time) const noexcept = 0;
};

class OtherScheduler : public Scheduler {
 public:
  int32_t nice = 0;

  void SetSchedAttr() const override {
    sched_attr attr = {};
    attr.size = sizeof(attr);

    attr.sched_flags = 0;
    attr.sched_nice = nice;           // Set the thread niceness
    attr.sched_policy = SCHED_OTHER;  // Set the scheduler policy

    auto ret = sched_setattr(0, &attr, 0);
    if (ret < 0) {
      throw std::runtime_error{std::string("failed to sched_setattr: ") + std::strerror(errno)};
    }
  }

  void Sleep(struct timespec /* next_wakeup_time */) const noexcept override {
    // Ignoring return value as man page says "In the Linux implementation, sched_yield() always succeeds."
    sched_yield();
  }
};

class FifoScheduler : public Scheduler {
 public:
  uint32_t priority = 0;

  void SetSchedAttr() const override {
    sched_attr attr = {};
    attr.size = sizeof(attr);

    attr.sched_flags = 0;
    attr.sched_nice = 0;
    attr.sched_priority = priority;  // Set the scheduler priority
    attr.sched_policy = SCHED_FIFO;  // Set the scheduler policy

    auto ret = sched_setattr(0, &attr, 0);
    if (ret < 0) {
      throw std::runtime_error{std::string("failed to sched_setattr: ") + std::strerror(errno)};
    }
  }

  void Sleep(struct timespec next_wakeup_time) const noexcept override {
    clock_nanosleep(CLOCK_MONOTONIC, TIMER_ABSTIME, &next_wakeup_time, nullptr);
  }
};

class DeadlineScheduler : public Scheduler {
 public:
  uint64_t sched_runtime_ns;
  uint64_t sched_deadline_ns;
  uint64_t sched_period_ns;

  void SetSchedAttr() const override {
    sched_attr attr = {};
    attr.size = sizeof(attr);

    attr.sched_flags = 0;
    attr.sched_nice = 0;
    attr.sched_priority = 0;  // No priority for SCHED_DEADLINE

    attr.sched_policy = SCHED_DEADLINE;  // Set the scheduler policy
    attr.sched_runtime = sched_runtime_ns;
    attr.sched_deadline = sched_deadline_ns;
    attr.sched_period = sched_period_ns;

    auto ret = sched_setattr(0, &attr, 0);
    if (ret < 0) {
      throw std::runtime_error{std::string("failed to sched_setattr: ") + std::strerror(errno)};
    }
  }

  void Sleep(struct timespec next_wakeup_time) const noexcept override {
    clock_nanosleep(CLOCK_MONOTONIC, TIMER_ABSTIME, &next_wakeup_time, nullptr);
  }
};

}  // namespace cactus_rt
#endif
