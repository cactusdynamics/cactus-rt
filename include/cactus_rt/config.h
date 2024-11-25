#ifndef CACTUS_RT_CONFIG_H_
#define CACTUS_RT_CONFIG_H_

#include <quill/Quill.h>

#include <memory>

#include "cactus_rt/scheduler.h"

namespace cactus_rt {

/**
 * @brief Config for the tracer
 */
struct TracerConfig {
  /**
   * @brief The CPU configuration for the tracer's background processing thread
   */
  std::vector<size_t> trace_aggregator_cpu_affinity;
};

/**
 * @brief The configuration required for an App
 */
struct AppConfig {
  /**
   * @brief Size of heap to reserve in bytes at program startup.
   */
  size_t heap_size = 0;

  /**
   * @brief The configuration for quill logging
   */
  quill::Config logger_config;

  /**
   * @brief The config for the tracer if enabled (CACTUS_RT_ENABLE_TRACING option in cmake)
   */
  TracerConfig tracer_config;
};

/**
 * @brief The configuration required for an SCHED_OTHER thread
 */
struct OtherThreadConfig {
  int32_t nice = 0;
};

/**
 * @brief The configuration required for a SCHED_FIFO thread
 */
struct FifoThreadConfig {
  uint32_t priority = 0;
};

/**
 * @brief The configuration required for a SCHED_DEADLINE thread
 */
struct DeadlineThreadConfig {
  uint64_t sched_runtime_ns;
  uint64_t sched_deadline_ns;
  uint64_t sched_period_ns;
};

struct ThreadTracerConfig {
  /**
   * @brief The size of the queue for the trace events for this thread.
   *
   * If the number of trace event overflows
   */
  uint32_t queue_size = 16384;

  /**
   * @brief Automatically trace the Loop function in CyclicThread.
   *
   * Enabling this will cause a slight performance overhead when trace session is started.
   */
  bool trace_loop = true;

  /**
   * @brief Automatically emit an event if the Loop function takes longer than the period.
   *
   * Enabling this will cause a slight performance overhead when trace session is started.
   */
  bool trace_overrun = true;

  /**
   * @brief Automatically trace the Sleep function in CyclicThread.
   *
   * Enabling this will cause a slight performance overhead when trace session is started.
   */
  bool trace_sleep = false;

  /**
   * @brief Trace the wakeup latency between when the thread should have woken up and when it actually woke up.
   *
   * Enabling this will cause a slight performance overhead when trace session is started.
   */
  bool trace_wakeup_latency = false;
};

/**
 * @brief The configuration required for a thread
 */
struct ThreadConfig {
  // A vector of CPUs this thread should run on. If empty, no CPU restrictions are set.
  std::vector<size_t> cpu_affinity;

  // The size of the stack for this thread. Defaults to 8MB.
  size_t stack_size = 8 * 1024 * 1024;

  ThreadTracerConfig tracer_config;

  // The scheduler type, default scheduler is SCHED_OTHER
  std::shared_ptr<Scheduler> scheduler = std::make_shared<OtherScheduler>();

  /**
   * @brief Set the thread scheduler to use the default (non-RT) scheduler
   * @param priority The thread nice value (19 to -20)
   */
  void SetOtherScheduler(int32_t nice = 0) {
    auto other_sched = std::make_shared<OtherScheduler>();
    other_sched->nice = nice;

    scheduler = other_sched;
  }

  /**
   * @brief Set the thread scheduler to be first-in-first-out (FIFO)
   * @param priority The thread priority (0 - 100)
   */
  void SetFifoScheduler(uint32_t priority) {
    auto fifo_sched = std::make_shared<FifoScheduler>();
    fifo_sched->priority = priority;

    scheduler = fifo_sched;
  }
};

struct CyclicThreadConfig : ThreadConfig {
  // The period of the cyclic thread in ns
  uint64_t period_ns = 1'000'000;

  /**
   * @brief Set the thread scheduler to be earliest deadline first (EDF)
   * @param sched_runtime_ns The runtime of that the task will receive each period
   * @param sched_deadline_ns The number of nanoseconds from the beginning of the period for which the runtime is available
   * @details Deadline scheduling is only applicable to cyclic threads. The period of the cyclic thread is used as the
   * EDF scheduling period.
   */
  void SetDeadlineScheduler(uint64_t sched_runtime_ns, uint64_t sched_deadline_ns) {
    if (!cpu_affinity.empty()) {
      throw std::runtime_error{"SCHED_DEADLINE cannot be used with cpu affinity, see sched_setattr(2)"};
    }
    auto deadline_sched = std::make_shared<DeadlineScheduler>();
    deadline_sched->sched_runtime_ns = sched_runtime_ns;
    deadline_sched->sched_deadline_ns = sched_deadline_ns;
    deadline_sched->sched_period_ns = period_ns;

    scheduler = deadline_sched;
  }
};

}  // namespace cactus_rt

#endif
