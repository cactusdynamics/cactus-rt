#ifndef CACTUS_RT_CONFIG_H_
#define CACTUS_RT_CONFIG_H_

#include <variant>

#include "quill/Quill.h"

namespace cactus_rt {

/**
 * @brief Config for the tracer
 */
struct TracerConfig {
  /**
   * @brief If the tracer starts enabled or not
   * TODO: make this actually work
   */
  bool starts_enabled = true;

  // TODO: custom sink support to skip the output file
  /**
   * @brief The output filename for the trace packet
   */
  std::string trace_output_filename = "data.perfetto";

  /**
   * @brief The CPU configuration for the tracer's background processing thread
   */
  std::vector<size_t> cpu_affinity;
};

/**
 * @brief The configuration required for an App
 */
struct AppConfig {
  // The name of the app
  const char* name = "RTApp";

  // Size of heap to reserve in bytes at program startup.
  size_t heap_size = 0;

  // Configuration for quill logging
  quill::Config logger_config;

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
  // The name of the thread
  std::string name = "Thread";

  // A vector of CPUs this thread should run on. If empty, no CPU restrictions are set.
  std::vector<size_t> cpu_affinity = {};

  // The size of the stack for this thread. Defaults to 8MB.
  size_t stack_size = 8 * 1024 * 1024;

  // The configuration for the scheduler (SCHED_OTHER, SCHED_FIFO, or SCHED_DEADLINE)
  std::variant<OtherThreadConfig, FifoThreadConfig, DeadlineThreadConfig> scheduler_config;

  ThreadTracerConfig thread_tracer;
};

struct CyclicThreadConfig : ThreadConfig {
  // The period of the cyclic thread in ns
  uint64_t period_ns = 1'000'000;
};

}  // namespace cactus_rt

#endif
