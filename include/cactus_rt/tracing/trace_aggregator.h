#ifndef TRACING_TRACE_AGGREGATOR
#define TRACING_TRACE_AGGREGATOR

#ifndef CACTUS_RT_TRACING_ENABLED
#include "trace_aggregator.disabled.h"
#else
#include <atomic>
#include <list>
#include <memory>
#include <mutex>
#include <string>
#include <thread>
#include <unordered_set>

#include "cactus_rt/logging.h"
#include "sink.h"
#include "thread_tracer.h"

namespace cactus_rt::tracing {

class TraceAggregator {
  using Trace = cactus_tracing::vendor::perfetto::protos::Trace;

  struct SessionState {
    const std::vector<size_t>   cpu_affinity;
    const std::shared_ptr<Sink> sink;

    // We use a std::thread and not a cactus_rt::Thread as cactus_rt::Thread has
    // dependency on this class, so we cannot have a circular dependency.
    std::thread      thread;
    std::atomic_bool stop_requested = false;

    // This is a set of sequence ids where the first packet has already been emitted.
    // If a sequence is not in here, the first packet emitted with have
    // first_packet_on_sequence = true, previous_packet_dropped = true, and
    // sequence_flags = SEQ_INCREMENTAL_STATE_CLEARED
    std::unordered_set<uint32_t> sequences_with_first_packet_emitted;

    explicit SessionState(std::shared_ptr<Sink> s, std::vector<size_t> affinity = {}) : cpu_affinity(affinity), sink(s) {}
  };

  const std::string process_name_;

  const uint64_t process_track_uuid_;

  cactus_rt::logging::Logger* logger_;  // Use the custom BoundedDroppingLogger

  // This mutex protects tracers_ and session_
  std::mutex mutex_;

  // This is a list of all known thread tracers. The background processing
  // thread will loop through this and pop all data from the queues.
  // Tracer is a friend class of ThreadTracer and thus can access all private
  // variables. These two structs are supposed to be tightly coupled so this is
  // no problem.
  std::list<std::shared_ptr<ThreadTracer>> tracers_;

  // This includes a single trace session state. It is recreated every time we create a new thread.
  std::unique_ptr<SessionState> session_ = nullptr;

 public:
  explicit TraceAggregator(std::string name);

  // Destructor is needed to flush the logger when this thread is destroyed
  ~TraceAggregator();

  // No copy no move
  TraceAggregator(const TraceAggregator&) = delete;
  TraceAggregator& operator=(const TraceAggregator&) = delete;
  TraceAggregator(TraceAggregator&&) = delete;
  TraceAggregator& operator=(TraceAggregator&&) = delete;

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
  void Start(std::shared_ptr<Sink> sink, std::vector<size_t> cpu_affinity = {});

  /**
   * @brief Stops the trace aggregator and reset it (this waits until the thread is shutdown)
   *
   * Calling this from multiple threads is likely undefined behavior.
   */
  void Stop() noexcept;

 private:
  cactus_rt::logging::Logger* Logger() noexcept;

  void Run();
  bool StopRequested() const noexcept;

  size_t TryDequeueOnceFromAllTracers(Trace& trace) noexcept;

  /**
   * Writes a trace into the sink.
   *
   * Must be called while session is active.
   */
  void WriteTrace(const Trace& trace) noexcept;

  /**
   * Adds the track event packet to an existing trace.
   *
   * Must be called while session is active. Requires locks to be held as it accesses session_.
   */
  void AddTrackEventPacketToTraceInternal(Trace& trace, ThreadTracer& thread_tracer, const TrackEventInternal& track_event_internal);

  /**
   *  Creates the initial process descriptor packet
   */
  Trace CreateProcessDescriptorPacket() const;

  /**
   * Creates a thread descriptor packet given a thread tracer.
   */
  Trace CreateThreadDescriptorPacket(const ThreadTracer& thread_tracer) const;
};
}  // namespace cactus_rt::tracing

#endif
#endif  // TRACING_TRACE_AGGREGATOR
