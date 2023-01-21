#ifndef CACTUS_RT_TRACING_H_
#define CACTUS_RT_TRACING_H_

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

  static TracerParameters FromEnv();
};

}  // namespace cactus_rt

#ifdef ENABLE_TRACING
#include <perfetto.h>

#include <memory>

// NOLINTBEGIN
// TODO: should we switch to PERFETTO_DEFINE_CATEGORIES_IN_NAMESPACE for Perfetto v32?
PERFETTO_DEFINE_CATEGORIES(
  perfetto::Category("cactus_rt"));
// NOLINTEND

namespace cactus_rt {
class InProcessTracer : public Tracer {
  std::unique_ptr<perfetto::TracingSession> tracing_session_;
  perfetto::TraceConfig                     trace_config_;
  const char*                               filename_;
  int                                       log_file_fd_;

 public:
  InProcessTracer(const char*             filename,
                  const TracerParameters& params);
  ~InProcessTracer() override;
  void Start() override;
  void Stop() override;
};
}  // namespace cactus_rt

#else

// Turn perfetto trace into no-ops
// TODO: there may be more macros to overwrite.
#define TRACE_EVENT(...)
#define TRACE_EVENT_BEGIN(...)
#define TRACE_EVENT_END(...)
#define TRACE_COUNTER(...)

#endif
#endif
