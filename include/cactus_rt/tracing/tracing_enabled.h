#ifndef CACTUS_RT_TRACING_GLOBALS_H_
#define CACTUS_RT_TRACING_GLOBALS_H_

#ifndef CACTUS_RT_TRACING_ENABLED
#include "tracing_enabled.disabled.h"
#else

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

inline bool IsTracingAvailable() noexcept {
  return true;
}

inline void EnableTracing() noexcept {
  tracing_enabled = true;
}

inline void DisableTracing() noexcept {
  tracing_enabled = false;
}
}  // namespace cactus_rt::tracing

#endif
#endif
