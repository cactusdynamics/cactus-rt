#ifndef CACTUS_RT_TRACING_TRACER_H_
#define CACTUS_RT_TRACING_TRACER_H_

#include <atomic>
#include <cstdint>
#include <deque>
#include <memory>
#include <mutex>
#include <thread>

#include "../thread.h"
#include "sink.h"
#include "thread_tracer.h"
#include "trace.pb.h"

// TODO: this feature is not fully fleshed out,
#ifndef CACTUS_RT_TRACING_STARTS_ENABLED
#define CACTUS_RT_TRACING_STARTS_ENABLED true
#endif

namespace cactus_rt::tracing {

/**
 * @brief This is the main tracer object where the ThreadTracers are registered.
 * Only one of these should be created per process.
 *
 * This is also the background thread where the trace packets are processed and
 * sinked.
 */
class Tracer : public cactus_rt::Thread<> {
  const char* process_name_;
  int32_t     process_pid_;
  uint64_t    process_track_uuid_;

  // Whether or not tracing is enabled. This can be dynamically controlled via
  // EnableTracing and DisableTracing.
  std::atomic_bool tracing_enabled_ = CACTUS_RT_TRACING_STARTS_ENABLED;

  // This mutex is for adding/removing thread tracers (sources) and
  // adding/removing sinks.  These operations do not interfere the emission of
  // of trace events and thus the emission of trace events are not protected by
  // this mutex. This is good, because having such a mutex is not
  // real-time-safe.
  //
  // Using this mutex, we can block the sinking of trace events while we change
  // the sources and sinks. Every time a source is added, we need to create
  // tracks and sink them into the protobuf trace message stream. Every time a
  // sink is added, we need to ensure all the track descriptor packets and other
  // sticky packets are emitted first before the events. This mutex helps
  // block the sinking of normal trace events so these track descriptor packets
  // can be written in the right order.
  std::mutex mutex_;

  // A vector of sinks that we can write the trace packets to.
  std::deque<std::unique_ptr<Sink>> sinks_;

  // This is a list of all known thread tracers. The background processing
  // thread will loop through this and pop all data from the queues.
  // Tracer is a friend class of ThreadTracer and thus can access all private
  // variables. These two structs are supposed to be tightly coupled so this is
  // no problem.
  //
  // Note we cannot use a std::vector because ThreadTracer contains an atomic
  // variable which cannot be a part of a vector which requires move/copy
  // constructors. A double-ended queue (deque) works tho.
  //
  // See: https://stackoverflow.com/questions/13193484/how-to-declare-a-vector-of-atomic-in-c
  std::deque<ThreadTracer> thread_tracers_;

  using Trace = cactus_tracing::vendor::perfetto::protos::Trace;

  // This is a vector of sticky trace packets that should always be emitted
  // when a new sink connects to the tracer. When a new sink connects to the
  // tracer, these packet will be sent first, before any events are sent.
  //
  // Packets that should be included here are things like the process/thread
  // track descriptor packets, or any other packets that affect the trace
  // globally and must be emitted before events are emitted.
  //
  // The list of packets only grow here (although shouldn't grow that much).
  std::deque<Trace> sticky_trace_packets_;

 public:
  /**
   * @brief Constructs a new Tracer. Should only be called once per process.
   *
   * @param process_name The name of this process
   * @param cpu_affinity CPU affinity for the background trace process thread.
   */
  Tracer(const char* process_name, std::vector<size_t> cpu_affinity);

  // No copy
  Tracer(const Tracer&) = delete;
  Tracer& operator=(const Tracer&) = delete;

  // No move
  Tracer(Tracer&&) noexcept = delete;
  Tracer& operator=(Tracer&&) noexcept = delete;

  /**
   * @brief Creates a new thread tracer. Each thread should only have one of
   * these and it should be called during initialization of the thread.
   */
  ThreadTracer& CreateThreadTracer(const char* thread_name, uint32_t queue_capacity = 16384);

  /**
   * @brief Adds a sink. Not real-time safe.
   */
  void RegisterSink(std::unique_ptr<Sink> sink);

  /**
   * @brief Dynamically enables tracing in a thread-safe manner.
   *
   * This feature is not fully functional. For example, should enable tracing
   * take a filename and reset the sinks so we don't write one giant file?
   */
  void EnableTracing() noexcept {
    tracing_enabled_.store(true, std::memory_order_relaxed);
  }

  /**
   * @brief Dynamically disables tracing in a thread-safe manner.
   *
   * This feature is not fully functional. For example, should enable tracing
   * take a filename and reset the sinks so we don't write one giant file?
   */
  void DisableTracing() noexcept {
    tracing_enabled_.store(false, std::memory_order_relaxed);
  }

  /**
   * @brief Checks if tracing is enabled. Thread safe and safe to call from RT.
   *
   * You don't usually need to call this manually, as the methods that emits
   * trace events on ThreadTracers will call this method internally.
   *
   * @returns true if tracing is enabled, false otherwise.
   */
  inline bool IsTracingEnabled() const noexcept {
    // TODO: give likely hint if CACTUS_RT_TRACING_STARTS_ENABLED is true...
    return tracing_enabled_.load(std::memory_order_relaxed);
  }

 protected:
  void Run() final;

 private:
  Trace CreateProcessDescriptorPacket() const;
  Trace CreateThreadDescriptorPacket(const ThreadTracer& thread_tracer) const;
  void  AddTrackEventPacketToTrace(Trace& trace, const ThreadTracer& thread_tracer, const TrackEventInternal& track_event_internal) const;
};
}  // namespace cactus_rt::tracing

#endif
