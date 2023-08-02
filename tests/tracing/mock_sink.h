#ifndef CACTUS_RT_TESTS_TRACING_MOCK_SINKS_H_
#define CACTUS_RT_TESTS_TRACING_MOCK_SINKS_H_

#include <mutex>
#include <vector>

#include "cactus_rt/tracing/sink.h"
#include "trace.pb.h"

// A mock sink where we log all the trace packets.
class MockSink : public cactus_rt::tracing::Sink {
  using Trace = cactus_tracing::vendor::perfetto::protos::Trace;

  std::mutex         mutex_;
  bool               broken_ = false;
  std::vector<Trace> logged_traces_;

 public:
  bool Write(const Trace& trace) final {
    std::scoped_lock lock(mutex_);
    if (broken_) {
      return false;
    }

    logged_traces_.push_back(trace);
    return true;
  }

  void SetBroken(bool broken) {
    broken_ = broken;
  }

  std::vector<Trace> LoggedTraces() {
    std::scoped_lock lock(mutex_);
    return logged_traces_;
  }
};

#endif
