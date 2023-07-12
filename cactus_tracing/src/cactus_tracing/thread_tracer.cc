#include "cactus_tracing/thread_tracer.h"

#include "cactus_tracing/utils.h"

namespace cactus_tracing {

ThreadTracer::ThreadTracer(const char* thread_name, int32_t thread_tid, uint32_t queue_capacity)
    : thread_name_(thread_name),
      thread_tid_(thread_tid),
      minimum_queue_capacity_(queue_capacity),
      queue_(queue_capacity),
      event_count_({0, 0}) {
  buffer_.reserve(queue_capacity);

  // TODO: is this kosher?
  static std::atomic_uint64_t thread_uuid = 1000;
  static std::atomic_uint32_t trusted_packet_sequence_id = 1000;

  thread_uuid_ = ++thread_uuid;
  trusted_packet_sequence_id_ = ++trusted_packet_sequence_id;
};

template <typename... Args>
bool ThreadTracer::Emit(Args&&... args) noexcept {
  bool success = queue_.try_emplace(std::forward<Args>(args)...);
  IncrementEventCount(!success);
  return success;
}

bool ThreadTracer::StartSpan(const char* name, const char* category) noexcept {
  return Emit(NowNs(), TrackEvent::Type::SLICE_BEGIN, name, category);
}

bool ThreadTracer::EndSpan() noexcept {
  return Emit(NowNs(), TrackEvent::Type::SLICE_END);
}

TraceSpan ThreadTracer::WithSpan(const char* name, const char* category) noexcept {
  TraceSpan span(this, name, category);
  return span;
}

EventCountData ThreadTracer::EventCount() noexcept {
  // TODO: relaxed memory order OK?
  return event_count_.load(std::memory_order_relaxed);
}

void ThreadTracer::IncrementEventCount(bool dropped) noexcept {
  // TODO: relaxed memory order OK?
  auto                old_count = event_count_.load(std::memory_order_relaxed);
  decltype(old_count) new_count;

  // TODO: Can this be done in a wait-free manner?
  // Theoretically only one thread should be writing to the variable which
  // means this should always succeed on the first try...
  do {
    new_count = old_count;
    if (dropped) {
      new_count.dropped_events++;
    }

    new_count.total_events++;
  } while (!event_count_.compare_exchange_weak(old_count, new_count, std::memory_order_relaxed));
}

TraceSpan::TraceSpan(ThreadTracer* tracer, const char* name, const char* category) : tracer_(tracer) {
  tracer_->StartSpan(name, category);
}

TraceSpan::~TraceSpan() {
  // TODO: is it possible for tracer_ to be nullptr? Maybe when the move
  // constructor happens? It's hard to save. Need to check.
  if (tracer_ != nullptr) {
    tracer_->EndSpan();
  }
}

}  // namespace cactus_tracing
