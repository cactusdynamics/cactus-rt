#ifndef CACTUS_RT_TESTS_TRACING_HELPERS_MOCK_SINKS_H_
#define CACTUS_RT_TESTS_TRACING_HELPERS_MOCK_SINKS_H_

#include <mutex>
#include <vector>

#include "cactus_rt/tracing/sink.h"
#include "trace.pb.h"

class MockSink : public cactus_rt::tracing::Sink {
  using Trace = cactus_tracing::vendor::perfetto::protos::Trace;

  std::mutex         mutex_;
  bool               broken_ = false;
  std::vector<Trace> logged_traces_;

 public:
  bool               Write(const Trace& trace) final;
  void               SetBroken(bool broken);
  std::vector<Trace> LoggedTraces();
  void               Clear();
};
#endif
