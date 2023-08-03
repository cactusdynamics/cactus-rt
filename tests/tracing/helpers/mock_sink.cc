#include "mock_sink.h"

using Trace = cactus_tracing::vendor::perfetto::protos::Trace;

bool MockSink::Write(const Trace& trace) {
  const std::scoped_lock lock(mutex_);
  if (broken_) {
    return false;
  }

  logged_traces_.push_back(trace);
  return true;
}

void MockSink::SetBroken(bool broken) {
  broken_ = broken;
}

std::vector<Trace> MockSink::LoggedTraces() {
  const std::scoped_lock lock(mutex_);
  return logged_traces_;
}

void MockSink::Clear() {
  const std::scoped_lock lock(mutex_);
  logged_traces_.clear();
}
