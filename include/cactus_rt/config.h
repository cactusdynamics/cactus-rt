#ifndef CACTUS_RT_CONFIG_H_
#define CACTUS_RT_CONFIG_H_

#include <quill/Quill.h>

#include <memory>
#include <string>

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
   * @brief The name of the app
   */
  const char* name = "RTApp";

  /**
   * @brief Size of heap to reserve in bytes at program startup.
   */
  size_t heap_size = 0;

  /**
   * @brief The configuration for quill logging
   */
  quill::Config logger_config;

  /**
   * @brief The config for the tracer if enabled (ENABLE_TRACING option in cmake)
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
  uint32_t queue_size = 16384;
};

/**
 * @brief The configuration required for a thread
 */
struct ThreadConfig {
  // Construct the ThreadConfig. Default scheduler is SCHED_OTHER
  ThreadConfig() : scheduler(std::make_shared<OtherScheduler>()) {}

  // A vector of CPUs this thread should run on. If empty, no CPU restrictions are set.
  std::vector<size_t> cpu_affinity = {};

  // The size of the stack for this thread. Defaults to 8MB.
  size_t stack_size = 8 * 1024 * 1024;

  ThreadTracerConfig         tracer_config;
  std::shared_ptr<Scheduler> scheduler;

  /**
   * @brief Set the thread scheduler to use the default (non-RT) scheduler
   * @param priority The thread nice value (19 to -20)
   */
  void SetOtherScheduler(int32_t nice) {
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
