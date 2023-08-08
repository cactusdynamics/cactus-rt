#ifndef CACTUS_TRACING_THREAD_TRACER_DISABLED_H_
#define CACTUS_TRACING_THREAD_TRACER_DISABLED_H_

#include <cstddef>
#include <cstdint>

namespace cactus_rt::tracing {
struct EventCountData {
};

class TraceSpan {
 public:
  TraceSpan() {}
  TraceSpan(const TraceSpan&) = delete;
  TraceSpan& operator=(const TraceSpan&) = delete;

  // Move OK, but copy is not?
  // TODO: check if this move constructor is necessary. It's likely that it doesn't need it.
  TraceSpan(TraceSpan&&) = default;
  TraceSpan& operator=(TraceSpan&&) = default;
};

class ThreadTracer {
 public:
  ThreadTracer(const char* /* name */, uint32_t /* queue_capacity */ = 16384) {}

  ThreadTracer(const ThreadTracer&) = delete;
  ThreadTracer& operator=(const ThreadTracer&) = delete;
  ThreadTracer(ThreadTracer&&) = delete;
  ThreadTracer& operator=(ThreadTracer&&) = delete;

  bool StartSpan(const char* /* name */, const char* /* category */ = nullptr) noexcept {
    return false;
  }

  bool EndSpan() noexcept {
    return false;
  }

  TraceSpan WithSpan(const char* /* name */, const char* /* category */ = nullptr) noexcept {
    TraceSpan span;
    return span;
  }

  bool InstantEvent(const char* /* name */, const char* /* category */ = nullptr) noexcept {
    return false;
  }

  inline EventCountData EventCount() const noexcept {
    EventCountData event_data;
    return event_data;
  }

  inline size_t QueueCapacity() const noexcept {
    return 0;
  }

  void SetTid() noexcept {}

 private:
  template <typename... Args>
  bool Emit(Args&&... /* args */) noexcept {
    return false;
  }

  void IncrementEventCount(bool /* dropped */) noexcept {}
};
}  // namespace cactus_rt::tracing

#endif
