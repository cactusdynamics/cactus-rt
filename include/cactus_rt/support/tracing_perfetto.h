#ifndef CACTUS_RT_TRACING_PERFETTO_H_
#define CACTUS_RT_TRACING_PERFETTO_H_

#include "tracing_common.h"

#ifdef ENABLE_TRACING

#include <perfetto.h>

#include <memory>

namespace cactus_rt {
class InProcessTracer : public Tracer {
  const char*                               filename_;
  TracerParameters                          params_;
  std::unique_ptr<perfetto::TracingSession> tracing_session_;
  perfetto::TraceConfig                     trace_config_;
  int                                       log_file_fd_;

 public:
  InProcessTracer(const char*      filename,
                  TracerParameters params);
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
