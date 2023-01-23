#ifndef CACTUS_RT_SUPPORT_TRACING_H_
#define CACTUS_RT_SUPPORT_TRACING_H_
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

constexpr const char* kTracingCategoryInternal = "cactus_rt";
constexpr const char* kTracingCategoryRealTime = "rt";
constexpr const char* kTracingCategoryNonRealTime = "nonrt";
constexpr const char* kTracingCategoryCustom1 = "custom1";
constexpr const char* kTracingCategoryCustom2 = "custom2";
constexpr const char* kTracingCategoryCustom3 = "custom3";
}  // namespace cactus_rt

#ifdef ENABLE_TRACING
#include <perfetto.h>

#include <memory>

// TODO: switch to PERFETTO_DEFINE_CATEOGIRES_IN_NAMESPACE for Perfetto v32
// NOLINTBEGIN
PERFETTO_DEFINE_CATEGORIES(
  perfetto::Category(cactus_rt::kTracingCategoryInternal).SetDescription("Events from the cactus-rt framework internals"),
  perfetto::Category(cactus_rt::kTracingCategoryRealTime).SetDescription("Custom application events from real-time threads"),
  perfetto::Category(cactus_rt::kTracingCategoryNonRealTime).SetDescription("Custom application events from non-real-time threads"),
  perfetto::Category(cactus_rt::kTracingCategoryCustom1).SetDescription("Arbitrary custom application events 1"),
  perfetto::Category(cactus_rt::kTracingCategoryCustom2).SetDescription("Arbitrary custom application events 2"),
  perfetto::Category(cactus_rt::kTracingCategoryCustom3).SetDescription("Arbitrary custom application events 3"));
// NOLINTEND

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
