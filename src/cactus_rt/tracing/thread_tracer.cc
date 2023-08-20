#include "cactus_rt/tracing/thread_tracer.h"

#include <mutex>

#include "cactus_rt/tracing/tracing_enabled.h"
#include "cactus_rt/utils.h"

using cactus_tracing::vendor::perfetto::protos::TrackEvent_Type_TYPE_INSTANT;
using cactus_tracing::vendor::perfetto::protos::TrackEvent_Type_TYPE_SLICE_BEGIN;
using cactus_tracing::vendor::perfetto::protos::TrackEvent_Type_TYPE_SLICE_END;

namespace {

uint64_t GenerateTrackUuid() noexcept {
  static std::atomic<uint64_t> track_uuid = 0;
  return ++track_uuid;
}

}  // namespace

namespace cactus_rt::tracing {
ThreadTracer::ThreadTracer(const char* name, uint32_t queue_capacity)
    : queue_(queue_capacity),
      name_(name),
      track_uuid_(GenerateTrackUuid()),
      event_count_(static_cast<uint32_t>(0), static_cast<uint32_t>(0)),
      // Should be ok to set the trusted packet sequence id to be the same if we
      // atomically generate these ids. Perfetto has more flexible architecture
      // as trace can come from multiple processes and be aggregated, which is
      // not possible here.
      trusted_packet_sequence_id_(static_cast<uint32_t>(track_uuid_)) {
  // need to be cached as queue_.max_capacity() is not free.
  // TODO: can max_capacity change? What do we do then? What if it decreases
  // after we read it? That said, the events emitted should never be close to
  // this value.
  queue_capacity_ = queue_.max_capacity();
}

bool ThreadTracer::StartSpan(const char* name, const char* category) noexcept {
  if (IsTracingEnabled()) {
    auto now = NowNs();
    return Emit(now, TrackEvent_Type_TYPE_SLICE_BEGIN, name, category);
  }

  return false;
}

bool ThreadTracer::EndSpan() noexcept {
  if (IsTracingEnabled()) {
    auto now = NowNs();
    return Emit(now, TrackEvent_Type_TYPE_SLICE_END);
  }

  return false;
}

bool ThreadTracer::InstantEvent(const char* name, const char* category) noexcept {
  if (IsTracingEnabled()) {
    return Emit(NowNs(), TrackEvent_Type_TYPE_INSTANT, name, category);
  }

  return false;
}

TraceSpan ThreadTracer::WithSpan(const char* name, const char* category, bool enabled) noexcept {
  TraceSpan span(this, name, category, enabled);
  return span;
}

template <typename... Args>
bool ThreadTracer::Emit(Args&&... args) noexcept {
  const bool success = queue_.try_emplace(std::forward<Args>(args)...);
  IncrementEventCount(!success);
  return success;
}

void ThreadTracer::IncrementEventCount(bool dropped) noexcept {
  // TODO: Can this be done in a wait-free manner?
  // Theoretically only one thread should be writing to the variable which
  // means this should always succeed on the first try...
  //
  // Note lambdas are real-time safe as it doesn't allocate. std::function
  // allocates but the Modify function is a template so it doesn't need to
  // allocate.
  event_count_.Modify([dropped](EventCountData old_data) noexcept {
    EventCountData new_data = old_data;
    if (dropped) {
      new_data.dropped_events++;
    }
    new_data.total_events++;
    return new_data;
  });
}

TraceSpan::TraceSpan(ThreadTracer* tracer, const char* name, const char* category, bool enabled) : thread_tracer_(enabled ? tracer : nullptr) {
  if (thread_tracer_ != nullptr) {
    thread_tracer_->StartSpan(name, category);
  }
}

TraceSpan::~TraceSpan() {
  if (thread_tracer_ != nullptr) {
    thread_tracer_->EndSpan();
  }
}
}  // namespace cactus_rt::tracing
