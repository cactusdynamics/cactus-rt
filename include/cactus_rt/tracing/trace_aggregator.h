#ifndef CACTUS_RT_TRACING_TRACE_AGGREGATOR_H_
#define CACTUS_RT_TRACING_TRACE_AGGREGATOR_H_

#ifndef CACTUS_RT_TRACING_ENABLED
#include "trace_aggregator.disabled.h"
#else
#include <quill/Quill.h>

#include <atomic>
#include <list>
#include <memory>
#include <mutex>
#include <string>
#include <thread>
#include <unordered_map>
#include <unordered_set>

#include "sink.h"
#include "thread_tracer.h"
#include "utils/string_interner.h"

namespace cactus_rt::tracing {

class TraceAggregatorManager;

class TraceAggregator2 {
  using Trace = cactus_tracing::vendor::perfetto::protos::Trace;

  // Need a reference to TraceAggregatorManager to get tracers and sinks.
  TraceAggregatorManager& manager_;

  // We use a std::thread and not a cactus_rt::Thread as cactus_rt::Thread has
  // dependency on this class, so we cannot have a circular dependency.
  std::thread      thread_;
  std::atomic_bool stop_requested_ = false;

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

  // This is a set of sequence ids where the first packet has already been emitted.
  // If a sequence is not in here, the first packet emitted with have
  // first_packet_on_sequence = true, previous_packet_dropped = true, and
  // sequence_flags = SEQ_INCREMENTAL_STATE_CLEARED
  std::unordered_set<uint32_t> sequences_with_first_packet_emitted_;

 public:
  TraceAggregator2(TraceAggregatorManager& manager);

  void Start();

  void RequestStop();

  void Join();

 private:
  void Run();
  bool StopRequested() const noexcept;
  void SetupCPUAffinityIfNecessary() const;

  /**
   * Adds the track event packet to an existing trace.
   *
   * Must be called while a lock is held.
   */
  void AddTrackEventPacketToTrace(Trace& trace, ThreadTracer& thread_tracer, const TrackEventInternal& track_event_internal);
};

class TraceAggregatorManager {
  using Trace = cactus_tracing::vendor::perfetto::protos::Trace;

  const std::string         process_name_;
  const std::vector<size_t> cpu_affinity_;
  const uint64_t            process_track_uuid_;
  quill::Logger*            logger_;

  std::mutex mutex_;

  // A list of sinks the output should be written to.
  std::list<std::shared_ptr<Sink>> sinks_;

  // This is a list of all known thread tracers. The background processing
  // thread will loop through this and pop all data from the queues.
  // Tracer is a friend class of ThreadTracer and thus can access all private
  // variables. These two structs are supposed to be tightly coupled so this is
  // no problem.
  std::list<std::shared_ptr<ThreadTracer>> tracers_;

  // Access to this requires mutex_ to be held.
  std::unique_ptr<TraceAggregator2> trace_aggregator_ = nullptr;

  friend class TraceAggregator2;

  quill::Logger* Logger();

 public:
  explicit TraceAggregatorManager(std::string process_name, std::vector<size_t> cpu_affinity = {});

  // No copy no move
  TraceAggregatorManager(const TraceAggregatorManager&) = delete;
  TraceAggregatorManager& operator=(const TraceAggregatorManager&) = delete;
  TraceAggregatorManager(TraceAggregatorManager&&) = delete;
  TraceAggregatorManager& operator=(TraceAggregatorManager&&) = delete;

  ~TraceAggregatorManager() = default;

  /**
   * @brief Adds a sink. Not real-time safe.
   */
  void RegisterSink(std::shared_ptr<Sink> sink);

  /**
   * @brief Removes a sink. Not real-time safe.
   */
  void DeregisterSink(const Sink* sink);

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
  void DeregisterThreadTracer(const ThreadTracer* tracer);

  /**
   * @brief Starts the trace aggregator if it didn't already start. No effect
   * if already started.
   */
  void Start();

  /**
   * @brief Requests the trace aggregator to stop if it started. No effect if
   * it is not started.
   */
  void RequestStop() noexcept;

  /**
   * @brief Joins the trace aggregator. No effect if not started.
   */
  void Join() noexcept;

 private:
  // The following methods are called by the TraceAggregator, not the Manager.
  /**
   *  Creates the initial process descriptor packet
   */
  Trace CreateProcessDescriptorPacket() const;

  /**
   * Creates a thread descriptor packet given a thread tracer.
   *
   * Must be called while a lock is held.
   */
  Trace CreateThreadDescriptorPacket(const ThreadTracer& thread_tracer) const;

  size_t TryDequeueOnceFromAllTracers(Trace& trace) noexcept;
  void   WriteTrace(const Trace& trace) noexcept;
};

class TraceAggregator {
  using Trace = cactus_tracing::vendor::perfetto::protos::Trace;
  using InternedData = cactus_tracing::vendor::perfetto::protos::InternedData;

  std::string         process_name_;
  std::vector<size_t> cpu_affinity_;
  uint64_t            process_track_uuid_;
  quill::Logger*      logger_;

  // We use a std::thread and not a cactus_rt::Thread as cactus_rt::Thread has
  // dependency on this class, so we cannot have a circular dependency.
  std::thread      thread_;
  std::atomic_bool stop_requested_ = false;

  std::mutex mutex_;

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

  // These are the interners for the event name and event categories to save
  // space on the output.
  utils::StringInterner event_name_interner_;
  utils::StringInterner event_category_interner_;

  // This is a map of trusted_sequence_id to InternedData.
  //
  // The InternedData is allocated directly here and kept for the duration of
  // the program. This is necessary in case we detect a packet loss, and we
  // would like to re-emit the interned data for that sequence so it can
  // continue.
  //
  // TODO: cap the amount of interned data to a maximum amount.
  std::unordered_map<uint32_t, std::vector<InternedData>> sequence_interned_data_;

  // This is a set of sequence ids where the first packet has already been emitted.
  // If a sequence is not in here, the first packet emitted with have
  // first_packet_on_sequence = true, previous_packet_dropped = true, and
  // sequence_flags = SEQ_INCREMENTAL_STATE_CLEARED
  std::unordered_set<uint32_t> sequences_with_first_packet_emitted_;

 public:
  explicit TraceAggregator(std::string name, std::vector<size_t> cpu_affinity = {});

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

  size_t TryDequeueOnceFromAllTracers(Trace& trace) noexcept;
  void   WriteTrace(const Trace& trace) noexcept;

  /**
   *  Creates the initial process descriptor packet
   */
  Trace CreateProcessDescriptorPacket() const;

  /**
   * Creates a thread descriptor packet given a thread tracer.
   *
   * Must be called while a lock is held.
   */
  Trace CreateThreadDescriptorPacket(const ThreadTracer& thread_tracer) const;

  /**
   * Adds the track event packet to an existing trace.
   *
   * Must be called while a lock is held.
   */
  void AddTrackEventPacketToTrace(Trace& trace, ThreadTracer& thread_tracer, const TrackEventInternal& track_event_internal);

  /**
   * Create the initial interned data packet if a new sink joins.
   *
   * Must be called while a lock is held.
   *
   * @param initial_timestamp The initial timestamp of the track, must be before
   * all other packets about to be written. Commonly this should be the
   * timestamp of the sticky packets.
   */
  std::optional<Trace> CreateInitialInternedDataPacket() const;
};
}  // namespace cactus_rt::tracing

#endif
#endif
