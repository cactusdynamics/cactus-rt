#include "cactus_rt/thread.h"

#include <sched.h>

#include <cerrno>
#include <cstring>
#include <ctime>
#include <iostream>
#include <stdexcept>

#include "cactus_rt/linux/sched_ext.h"

namespace cactus_rt {

namespace {
// TODO: Pass thread config instead of CPU affinity
void SetSchedAttr(const SchedulerConfigVariant& config_variant, const std::vector<size_t>& cpu_affinity) {
  // Populate sched_attr based on the type of scheduler config provided
  sched_attr attr = {};
  attr.size = sizeof(attr);

  if (std::holds_alternative<OtherThreadConfig>(config_variant)) {
    auto config = std::get<OtherThreadConfig>(config_variant);

    attr.sched_flags = 0;
    attr.sched_nice = config.nice;    // Set the thread niceness
    attr.sched_policy = SCHED_OTHER;  // Set the scheduler policy
  } else if (std::holds_alternative<FifoThreadConfig>(config_variant)) {
    auto config = std::get<FifoThreadConfig>(config_variant);

    attr.sched_flags = 0;
    attr.sched_nice = 0;
    attr.sched_priority = config.priority;  // Set the scheduler priority
    attr.sched_policy = SCHED_FIFO;         // Set the scheduler policy
  } else if (std::holds_alternative<DeadlineThreadConfig>(config_variant)) {
    if (!cpu_affinity.empty()) {
      throw std::runtime_error{"SCHED_DEADLINE cannot be used with cpu affinity, see sched_setattr(2)"};
    }

    auto config = std::get<DeadlineThreadConfig>(config_variant);

    attr.sched_flags = 0;
    attr.sched_nice = 0;
    attr.sched_priority = 0;  // No priority for SCHED_DEADLINE

    attr.sched_policy = SCHED_DEADLINE;  // Set the scheduler policy
    attr.sched_runtime = config.sched_runtime_ns;
    attr.sched_deadline = config.sched_deadline_ns;
    attr.sched_period = config.sched_period_ns;
  }

  auto ret = sched_setattr(0, &attr, 0);
  if (ret < 0) {
    throw std::runtime_error{std::string("failed to sched_setattr: ") + std::strerror(errno)};
  }
}
}  // namespace

void* Thread::RunThread(void* data) {
  auto* thread = static_cast<Thread*>(data);
  SetSchedAttr(thread->scheduler_config_, thread->cpu_affinity_);

  thread->BeforeRun();
  thread->Run();
  thread->AfterRun();
  return nullptr;
}

void Thread::Start(int64_t start_monotonic_time_ns) {
  start_monotonic_time_ns_ = start_monotonic_time_ns;

  pthread_attr_t attr;

  // Initialize the pthread attribute
  int ret = pthread_attr_init(&attr);
  if (ret != 0) {
    throw std::runtime_error(std::string("error in pthread_attr_init: ") + std::strerror(ret));
  }

  // Set a stack size
  //
  // Note the stack is prefaulted if mlockall(MCL_FUTURE | MCL_CURRENT) is
  // called, which under this app framework should be.
  //
  // Not even sure if there is an optimizer-safe way to prefault the stack
  // anyway, as the compiler optimizer may realize that buffer is never used
  // and thus will simply optimize it out.
  ret = pthread_attr_setstacksize(&attr, stack_size_);
  if (ret != 0) {
    throw std::runtime_error(std::string("error in pthread_attr_setstacksize: ") + std::strerror(ret));
  }

  // Setting CPU mask
  if (!cpu_affinity_.empty()) {
    cpu_set_t cpuset;
    CPU_ZERO(&cpuset);
    for (auto cpu : cpu_affinity_) {
      CPU_SET(cpu, &cpuset);
    }

    ret = pthread_attr_setaffinity_np(&attr, sizeof(cpu_set_t), &cpuset);
    if (ret != 0) {
      throw std::runtime_error(std::string("error in pthread_attr_setaffinity_np: ") + std::strerror(ret));
    }
  }

  ret = pthread_create(&thread_, &attr, &Thread::RunThread, this);
  if (ret != 0) {
    throw std::runtime_error(std::string("error in pthread_create: ") + std::strerror(ret));
  }
}

int Thread::Join() {
  return pthread_join(thread_, nullptr);
}
}  // namespace cactus_rt
