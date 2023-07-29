#ifndef CACTUS_RT_TRACING_GLOBALS_H_
#define CACTUS_RT_TRACING_GLOBALS_H_

#include <atomic>

namespace cactus_rt::tracing {
extern std::atomic_bool tracing_enabled;

void EnableTracing() noexcept {
  tracing_enabled.store(true, std::memory_order_relaxed);
}

void DisableTracing() noexcept {
  tracing_enabled.store(false, std::memory_order_relaxed);
}

inline bool IsTracingEnabled() noexcept {
  return tracing_enabled.load(std::memory_order_relaxed);
}

}  // namespace cactus_rt::tracing

#endif
