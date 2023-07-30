#ifndef CACTUS_RT_TRACING_GLOBALS_H_
#define CACTUS_RT_TRACING_GLOBALS_H_

#include <atomic>

namespace cactus_rt::tracing {
// This is a process-level atomic because we don't want a dependency of
// ThreadTracer and TraceAggregator to App.
extern std::atomic_bool tracing_enabled;

/**
 * @brief Checks if tracing is enabled
 */
inline bool IsTracingEnabled() noexcept {
  return tracing_enabled.load(std::memory_order_relaxed);
}

}  // namespace cactus_rt::tracing

#endif
