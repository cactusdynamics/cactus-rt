#ifndef CACTUS_TRACING_THREAD_TRACER_H_
#define CACTUS_TRACING_THREAD_TRACER_H_

#include <readerwriterqueue.h>

#include <cstdint>

#include "../experimental/lockless/atomic_message.h"
#include "track_event_internal.h"

namespace cactus_rt::tracing {
struct EventCountData {
  uint32_t total_events = 0;
  uint32_t dropped_events = 0;

  EventCountData() = default;
  EventCountData(uint32_t total, uint32_t dropped) : total_events(total), dropped_events(dropped) {}
};

// Required forward declarations
class TraceSpan;
class TraceAggregator;

/**
 * @brief A tracer for a single thread. Creates a single track in the trace
 * output. Should only have one per thread.
 */
class ThreadTracer {
  friend class TraceAggregator;

  moodycamel::ReaderWriterQueue<TrackEventInternal> queue_;

  const char* name_;
  uint64_t    track_uuid_;

  // TODO: relaxed memory order OK? It's not a control variable nor do any other
  // variables depend on this variable.
  cactus_rt::experimental::lockless::AtomicMessage<EventCountData, std::memory_order_relaxed> event_count_;

  // This is not the same as the passed in queue size as that is the minimum
  // queue size
  size_t queue_capacity_;

  uint32_t trusted_packet_sequence_id_;

  // This cannot be initialized when the ThreadTracer is created and must be
  // initialized when the thread actually starts running.
  int32_t tid_ = 0;

 public:
  ThreadTracer(const char* name, uint32_t queue_capacity = 16384);

  ThreadTracer(const ThreadTracer&) = delete;
  ThreadTracer& operator=(const ThreadTracer&) = delete;
  ThreadTracer(ThreadTracer&&) = delete;
  ThreadTracer& operator=(ThreadTracer&&) = delete;

  bool      StartSpan(const char* name, const char* category = nullptr) noexcept;
  bool      EndSpan() noexcept;
  TraceSpan WithSpan(const char* name, const char* category = nullptr) noexcept;
  bool      InstantEvent(const char* name, const char* category = nullptr) noexcept;

  inline EventCountData EventCount() const noexcept { return event_count_.Read(); }
  inline size_t         QueueCapacity() const noexcept { return queue_capacity_; }

  /**
   * @brief Get and memorize the thread id. Should only be called from the
   *        thread by Thread::RunThread.
   *
   * @private
   */
  void SetTid() noexcept { tid_ = gettid(); }

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
