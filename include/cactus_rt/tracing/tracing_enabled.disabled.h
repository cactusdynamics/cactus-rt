#ifndef CACTUS_RT_TRACING_TRACING_ENABLED_DISABLED_H_
#define CACTUS_RT_TRACING_TRACING_ENABLED_DISABLED_H_
namespace cactus_rt::tracing {
inline bool IsTracingEnabled() noexcept {
  return false;
}

inline bool IsTracingAvailable() noexcept {
  return false;
}

inline void EnableTracing() noexcept {}

inline void DisableTracing() noexcept {}

}  // namespace cactus_rt::tracing
#endif
