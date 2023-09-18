#ifndef CACTUS_RT_TRACING_TRACE_AGGREGATOR_DISABLED_H_
#define CACTUS_RT_TRACING_TRACE_AGGREGATOR_DISABLED_H_

#include <memory>
#include <string>
#include <vector>

#include "sink.disabled.h"
#include "thread_tracer.disabled.h"

namespace cactus_rt::tracing {
class TraceAggregator {
 public:
  explicit TraceAggregator(std::string /* name */, std::vector<size_t> /* cpu_affinity */) {}

  TraceAggregator(const TraceAggregator&) = delete;
  TraceAggregator& operator=(const TraceAggregator&) = delete;
  TraceAggregator(TraceAggregator&&) = delete;
  TraceAggregator& operator=(TraceAggregator&&) = delete;

  void RegisterSink(std::shared_ptr<Sink> /* sink */) {}

  void RegisterThreadTracer(std::shared_ptr<ThreadTracer> /* tracer */) {}

  void DeregisterThreadTracer(const std::shared_ptr<ThreadTracer>& /* tracer */) {}

  void Start(){};

  void RequestStop() noexcept {}

  void Join() noexcept {}
};
}  // namespace cactus_rt::tracing
#endif
