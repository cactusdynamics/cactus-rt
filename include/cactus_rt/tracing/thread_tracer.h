#ifndef CACTUS_RT_TRACING_THREAD_TRACER_H_
#define CACTUS_RT_TRACING_THREAD_TRACER_H_

#include <readerwriterqueue.h>

#include <cstdint>

#include "../experimental/lockless/atomic_message.h"
#include "track_event_internal.h"

namespace cactus_rt::tracing {
// Forward declaration to avoid circular dependencies
class Tracer;
class TraceSpan;

struct EventCountData {
  uint32_t total_events;
  uint32_t dropped_events;
};

/**
 * @brief A tracer for a single thread. Creates a single track in the trace
 * output. Should only have one per thread.
 */
class ThreadTracer {
  friend class Tracer;

  const Tracer& tracer_;

  const char* thread_name_;
  int32_t     thread_tid_;
  uint64_t    thread_track_uuid_;
  uint32_t    trusted_packet_sequence_id_;

  uint32_t                                          queue_capacity_;
  moodycamel::ReaderWriterQueue<TrackEventInternal> queue_;

  cactus_rt::experimental::lockless::AtomicMessage<EventCountData> event_count_;

 public:
  ThreadTracer(
    const Tracer& tracer,
    const char*   thread_name,
    int32_t       thread_tid,
    uint64_t      thread_track_uuid,
    uint32_t      trusted_packet_sequence_id,
    uint32_t      queue_capacity = 16384  // TODO: probably need a better way to specify this
  );

  bool      StartSpan(const char* name, const char* category = nullptr) noexcept;
  bool      EndSpan() noexcept;
  TraceSpan WithSpan(const char* name, const char* category = nullptr) noexcept;
  bool      InstantEvent(const char* name, const char* category = nullptr) noexcept;

  template <typename... Args>
  bool Emit(Args&&... args) noexcept;

  inline EventCountData EventCount() noexcept {
    return event_count_.Read();
  }

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

}  // namespace cactus_rt::tracing
#endif
