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
  uint32_t total_events = 0;
  uint32_t dropped_events = 0;

  EventCountData() = default;
  EventCountData(uint32_t total, uint32_t dropped) : total_events(total), dropped_events(dropped) {}
};

/**
 * @brief A tracer for a single thread. Creates a single track in the trace
 * output. Should only have one per thread.
 */
class ThreadTracer {
  friend class Tracer;

  const Tracer& tracer_;

  const char* thread_name_;
  int32_t     thread_tid_ = 0;
  uint64_t    thread_track_uuid_;
  uint32_t    trusted_packet_sequence_id_;

  size_t                                            queue_capacity_;
  moodycamel::ReaderWriterQueue<TrackEventInternal> queue_;

  // TODO: relaxed memory order OK? It's not a control variable nor do any other
  // variables depend on this variable.
  cactus_rt::experimental::lockless::AtomicMessage<EventCountData, std::memory_order_relaxed> event_count_;

 public:
  /**
   * @brief Do not use this constructor. Use Tracer::CreateThreadTracer instead.
   *
   * The only reason this is public is because vector::emplace_back works poorly
   * with a private constructor and I don't want to go through the song and
   * dance of that.
   *
   * @private
   */
  ThreadTracer(
    const Tracer& tracer,
    const char*   thread_name,
    uint64_t      thread_track_uuid,
    uint32_t      trusted_packet_sequence_id,
    uint32_t      queue_capacity = 16384  // TODO: probably need a better way to specify this
  );

  bool      StartSpan(const char* name, const char* category = nullptr) noexcept;
  bool      EndSpan() noexcept;
  TraceSpan WithSpan(const char* name, const char* category = nullptr) noexcept;
  bool      InstantEvent(const char* name, const char* category = nullptr) noexcept;

  /**
   * @brief Sets the thread tid for this ThreadTracer.
   *
   * The reason this is delayed is because we create the ThreadTracer on thread
   * creation, but the tid is not available until the thread starts.
   */
  inline void SetThreadTid(int32_t thread_tid) {
    thread_tid_ = thread_tid;
  }

  inline EventCountData EventCount() const noexcept {
    return event_count_.Read();
  }

  inline size_t QueueCapacity() const noexcept {
    return queue_capacity_;
  }

 private:
  template <typename... Args>
  bool Emit(Args&&... args) noexcept;

  void IncrementEventCount(bool dropped) noexcept;
};

class TraceSpan {
  friend class ThreadTracer;
  ThreadTracer* thread_tracer_;

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
