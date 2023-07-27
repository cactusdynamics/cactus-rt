#include "cactus_rt/tracing/thread_tracer.h"

#include "cactus_rt/tracing/tracer.h"
#include "cactus_rt/utils.h"

using cactus_tracing::vendor::perfetto::protos::TrackEvent_Type_TYPE_INSTANT;
using cactus_tracing::vendor::perfetto::protos::TrackEvent_Type_TYPE_SLICE_BEGIN;
using cactus_tracing::vendor::perfetto::protos::TrackEvent_Type_TYPE_SLICE_END;

namespace cactus_rt::tracing {

ThreadTracer::ThreadTracer(
  const Tracer& tracer,
  const char*   thread_name,
  uint64_t      thread_track_uuid,
  uint32_t      trusted_packet_sequence_id,
  uint32_t      queue_capacity
) : tracer_(tracer),
    thread_name_(thread_name),
    thread_track_uuid_(thread_track_uuid),
    trusted_packet_sequence_id_(trusted_packet_sequence_id),
    queue_(queue_capacity),
    event_count_(static_cast<uint32_t>(0), static_cast<uint32_t>(0)) {
  // need to be cached as max_capacity is not free.
  // TODO: can max_capacity change? What do we do then? What if it decreases
  // after we read it? That said, the events emitted should never be close to
  // this value.
  queue_capacity_ = queue_.max_capacity();
}

bool ThreadTracer::StartSpan(const char* name, const char* category) noexcept {
  if (tracer_.IsTracingEnabled()) {
    auto now = NowNs();
    return Emit(now, TrackEvent_Type_TYPE_SLICE_BEGIN, name, category);
  }

  // TODO: determine if this should be false or true...
  return true;
}

bool ThreadTracer::EndSpan() noexcept {
  if (tracer_.IsTracingEnabled()) {
    auto now = NowNs();
    return Emit(now, TrackEvent_Type_TYPE_SLICE_END);
  }

  return true;
}

bool ThreadTracer::InstantEvent(const char* name, const char* category) noexcept {
  if (tracer_.IsTracingEnabled()) {
    return Emit(NowNs(), TrackEvent_Type_TYPE_INSTANT, name, category);
  }

  return true;
}

TraceSpan ThreadTracer::WithSpan(const char* name, const char* category) noexcept {
  TraceSpan span(this, name, category);
  return span;
}

template <typename... Args>
bool ThreadTracer::Emit(Args&&... args) noexcept {
  bool success = queue_.try_emplace(std::forward<Args>(args)...);
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
  event_count_.Modify([dropped](EventCountData old_data) {
    EventCountData new_data = old_data;
    if (dropped) {
      new_data.dropped_events++;
    }
    new_data.total_events++;
    return new_data;
  });
}

TraceSpan::TraceSpan(ThreadTracer* tracer, const char* name, const char* category) : thread_tracer_(tracer) {
  thread_tracer_->StartSpan(name, category);
}

TraceSpan::~TraceSpan() {
  // TODO: is it possible for thread_tracer_ to be nullptr? Maybe when the move
  // constructor happens? It's hard to save. Need to check.
  if (thread_tracer_ != nullptr) {
    thread_tracer_->EndSpan();
  }
}

}  // namespace cactus_rt::tracing
