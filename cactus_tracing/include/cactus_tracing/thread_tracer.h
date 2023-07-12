#ifndef CACTUS_TRACING_THREAD_TRACER_H_
#define CACTUS_TRACING_THREAD_TRACER_H_

#include <readerwriterqueue.h>

#include <atomic>
#include <cstdint>
#include <utility>
#include <vector>

#include "track_event.h"

using moodycamel::ReaderWriterQueue;

namespace cactus_tracing {

// Forward declaration to avoid circular dependencies
class TraceSpan;
class Tracer;

struct EventCountData {
  uint32_t total_events;
  uint32_t dropped_events;
};

/**
 * The tracer responsible for a single thread, and therefore a single track.
 */
class ThreadTracer {
  friend class Tracer;

  const char* thread_name_;
  int32_t     thread_tid_;

  uint32_t                      minimum_queue_capacity_;
  ReaderWriterQueue<TrackEvent> queue_;

  // Using vector as a buffer for now. Maybe a better idea to use another
  // queue? That's what Quill does. Maybe it will get better performance but
  // not 100% sure. This is OK for now tho.
  std::vector<TrackEvent> buffer_;

  using AtomicMessageCount = std::atomic<EventCountData>;
  AtomicMessageCount event_count_;
  static_assert(AtomicMessageCount::is_always_lock_free);

  uint64_t thread_uuid_;
  uint32_t trusted_packet_sequence_id_;

 public:
  ThreadTracer(const char* thread_name, int32_t thread_tid, uint32_t queue_capacity = 16384);

  bool      StartSpan(const char* name, const char* category = nullptr) noexcept;
  bool      EndSpan() noexcept;
  TraceSpan WithSpan(const char* name, const char* category = nullptr) noexcept;

  bool Event(const char* name, const char* category = nullptr) noexcept;

  template <typename... Args>
  bool Emit(Args&&... args) noexcept;

  EventCountData EventCount() noexcept;

 private:
  void IncrementEventCount(bool dropped) noexcept;
};

class TraceSpan {
  friend class ThreadTracer;
  ThreadTracer* tracer_;

  TraceSpan(ThreadTracer* tracer, const char* name, const char* category = nullptr);

 public:
  ~TraceSpan();

  TraceSpan(const TraceSpan&) = delete;
  TraceSpan& operator=(const TraceSpan&) = delete;

  // Move OK, but copy is not?
  // TODO: check if this move constructor is necessary. It's likely that it doesn't need it.
  TraceSpan(TraceSpan&&) = default;
  TraceSpan& operator=(TraceSpan&&) = default;
};
}  // namespace cactus_tracing

#endif
