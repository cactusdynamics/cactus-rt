#ifndef CACTUS_RT_TRACING_TRACE_AGGREGATOR_H_
#define CACTUS_RT_TRACING_TRACE_AGGREGATOR_H_

#include <quill/Quill.h>

#include <atomic>
#include <list>
#include <memory>
#include <mutex>
#include <thread>

#include "sink.h"
#include "thread_tracer.h"

namespace cactus_rt::tracing {

class TraceAggregator {
  using Trace = cactus_tracing::vendor::perfetto::protos::Trace;

  const char*         process_name_;
  std::vector<size_t> cpu_affinity_;
  uint64_t            process_track_uuid_;
  quill::Logger*      logger_;

  // We use a std::thread and not a cactus_rt::Thread as cactus_rt::Thread has
  // dependency on this class, so we cannot have a circular dependency.
  std::thread      thread_;
  std::atomic_bool stop_requested_ = false;
  std::mutex       mutex_;

  // A list of sinks the output should be written to.
  std::list<std::shared_ptr<Sink>> sinks_;

  // This is a list of all known thread tracers. The background processing
  // thread will loop through this and pop all data from the queues.
  // Tracer is a friend class of ThreadTracer and thus can access all private
  // variables. These two structs are supposed to be tightly coupled so this is
  // no problem.
  std::list<std::shared_ptr<ThreadTracer>> tracers_;

  // This is a vector of sticky trace packets that should always be emitted
  // when a new sink connects to the tracer. When a new sink connects to the
  // tracer, these packet will be sent first, before any events are sent.
  //
  // Packets that should be included here are things like the process/thread
  // track descriptor packets, or any other packets that affect the trace
  // globally and must be emitted before events are emitted.
  //
  // The list of packets only grow here (although shouldn't grow that much).
  std::list<Trace> sticky_trace_packets_;

 public:
  explicit TraceAggregator(const char* name, std::vector<size_t> cpu_affinity);

  // No copy no move
  TraceAggregator(const TraceAggregator&) = delete;
  TraceAggregator& operator=(const TraceAggregator&) = delete;
  TraceAggregator(TraceAggregator&&) = delete;
  TraceAggregator& operator=(TraceAggregator&&) = delete;

  /**
   * @brief Adds a sink. Not real-time safe.
   */
  void RegisterSink(std::shared_ptr<Sink> sink);

  /**
   * @brief Adds a thread tracer. Not real-time safe.
   *
   * The ThreadTracer at this point must have its name_ and tid_ filled out.
   * This should occur before the thread starts running and trace starts
   * accumulating.
   */
  void RegisterThreadTracer(std::shared_ptr<ThreadTracer> tracer);

  /**
   * @brief Removes a thread tracer. Not real-time safe.
   */
  void DeregisterThreadTracer(const std::shared_ptr<ThreadTracer>& tracer);

  /**
   * @brief Starts the trace aggregator background thread
   */
  void Start();

  /**
   * @brief Requests the trace aggregator to stop
   */
  void RequestStop() noexcept;

  /**
   * @brief Joins the thread
   */
  void Join() noexcept;

 private:
  quill::Logger* Logger() noexcept;

  void Run();
  bool StopRequested() const noexcept;

  void SetupCPUAffinityIfNecessary() const;

  Trace CreateProcessDescriptorPacket() const;
  Trace CreateThreadDescriptorPacket(const ThreadTracer& thread_tracer) const;
  void  AddTrackEventPacketToTrace(Trace& trace, const ThreadTracer& thread_tracer, const TrackEventInternal& track_event_internal) const;
};
}  // namespace cactus_rt::tracing

#endif
