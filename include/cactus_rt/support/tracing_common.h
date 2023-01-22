#ifndef CACTUS_RT_SUPPORT_TRACING_COMMON_H_
#define CACTUS_RT_SUPPORT_TRACING_COMMON_H_
#include <cstdint>

namespace cactus_rt {

class Tracer {
 public:
  Tracer() = default;
  virtual ~Tracer() = default;

  Tracer(const Tracer&) = delete;
  Tracer& operator=(const Tracer&) = delete;

  Tracer(Tracer&&) = delete;
  Tracer& operator=(Tracer&&) = delete;

  virtual void Start() = 0;
  virtual void Stop() = 0;
};

struct TracerParameters {
  uint32_t bufsize = 16 * 1024;
  uint32_t file_write_period_ms = 2000;
  uint32_t flush_period_ms = 2000;

  static TracerParameters FromEnv() {
    TracerParameters params;

    // TODO: FIX ME BEFORE MERGE: read the parameters from the environment

    return params;
  }
};

constexpr const char* kTracingCategory = "cactus_rt";

}  // namespace cactus_rt
#endif
