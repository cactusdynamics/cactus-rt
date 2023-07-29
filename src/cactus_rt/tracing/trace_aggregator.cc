#include "cactus_rt/tracing/trace_aggregator.h"

#include <chrono>

using Trace = cactus_tracing::vendor::perfetto::protos::Trace;
using TrackDescriptor = cactus_tracing::vendor::perfetto::protos::TrackDescriptor;
using ThreadDescriptor = cactus_tracing::vendor::perfetto::protos::ThreadDescriptor;
using ProcessDescriptor = cactus_tracing::vendor::perfetto::protos::ProcessDescriptor;
using TrackEvent = cactus_tracing::vendor::perfetto::protos::TrackEvent;

using namespace std::chrono_literals;

namespace cactus_rt::tracing {
TraceAggregator::TraceAggregator(TraceAggregatorConfig config)
    : config_(config),
      process_track_uuid_(static_cast<uint64_t>(getpid())),
      logger_(quill::create_logger("__trace_aggregator__")) {
  this->sticky_trace_packets_.push_back(CreateProcessDescriptorPacket());
}

void TraceAggregator::RegisterSink(std::unique_ptr<Sink> sink) {
  // RegisterSink is mutually exclusive with RegisterThreadTracer and writing
  // metric data from queues to the sinks. This is because we need to ensure the
  // first trace packets on any new sink must be the track descriptors for all
  // known tracks. We also need to ensure that writing to sinks only happen on
  // one thread with mutual exclusion to avoid data race.
  const std::scoped_lock lock(mutex_);

  for (const auto& trace : this->sticky_trace_packets_) {
    // TODO: deal with errors
    sink->Write(trace);
  }

  sinks_.push_back(std::move(sink));
}

void TraceAggregator::RegisterThreadTracer(std::shared_ptr<ThreadTracer> tracer) {
  if (tracer->tid_ == 0) {
    LOG_WARNING(Logger(), "thread {} does not have a valid tid. this shouldn't have happened and is likely a bug", tracer->name_);
  }

  // RegisterThreadTracer is mutually exclusive with RegisterSink and writing of
  // metric data. This is because we need to make sure the thread track
  // descriptor packet always appears in the data stream before the trace data
  // packets. To do this, we lock out RegisterSink and metric writing so we
  // can broadcast the thread tracer to all known sinks. Further, since we are
  // writing to sinks here, only a single thread may do it at a time thus also
  // requiring the lock.
  const std::scoped_lock lock(mutex_);

  tracers_.push_back(tracer);

  auto trace = CreateThreadDescriptorPacket(*tracer);
  for (auto& sink : sinks_) {
    // TODO: deal with errors
    sink->Write(trace);
  }

  // Move the trace packet to the sticky packets so newly registered sinks gets
  // this packet when they get registered.
  this->sticky_trace_packets_.push_back(std::move(trace));
}

void TraceAggregator::Start() {
  // TODO: CPU affinity!
  std::thread thread{&TraceAggregator::Run, this};
  thread_.swap(thread);
}

void TraceAggregator::RequestStop() noexcept {
  stop_requested_.store(true, std::memory_order_relaxed);
}

void TraceAggregator::Join() noexcept {
  thread_.join();
}

quill::Logger* TraceAggregator::Logger() noexcept {
  return logger_;
}

void TraceAggregator::Run() {
  // TODO: major refactor required

  while (!StopRequested()) {
    // This lock is needed as when we are writing packets into sinks, we don't
    // want new thread tracers and sinks to be created or registered as that
    // can cause potential data loss. This lock is NOT for dequeueing from the
    // thread tracer queues, as expected.
    const std::scoped_lock lock(mutex_);

    int   tracers_with_events = 0;
    Trace trace;

    for (auto& tracer : tracers_) {
      TrackEventInternal event;
      if (!tracer->queue_.try_dequeue(event)) {
        // No event in this queue.
        continue;
      }

      tracers_with_events++;
      AddTrackEventPacketToTrace(trace, *tracer, event);
    }

    if (tracers_with_events > 0) {
      for (auto& sink : sinks_) {
        sink->Write(trace);
      }
    }

    // TODO: check if there are any dropped packets since last time we checked

    if (tracers_with_events == 0) {
      // No events from any tracers! We can sleep and let the queues accumulate a bit.
      // TODO: customize this sleep period
      std::this_thread::sleep_for(10ms);
    }
    // If there are events then we want to write as fast as possible.
  }

  // TODO: likely need to take a large lock here when flushing?

  // Need to empty all the remaining events in the queue
  // This code is a bit redundant, but works for now. In the long term, this
  // whole thread probably has to be rewritten to better optimize for throughput
  // and possibly ordering problems.
  // TODO: right now we accumulate a giant Trace message and write it all
  // together. In the future there should be batch writing.
  bool  has_events = false;
  Trace trace;
  while (true) {
    int tracers_with_events = 0;

    for (auto& tracer : tracers_) {
      TrackEventInternal event;
      if (!tracer->queue_.try_dequeue(event)) {
        continue;
      }

      tracers_with_events++;
      AddTrackEventPacketToTrace(trace, *tracer, event);
      has_events = true;
    }

    if (tracers_with_events == 0) {
      break;
    }
  }

  if (has_events) {
    for (auto& sink : sinks_) {
      // TODO: errors
      sink->Write(trace);
    }
  }
}

bool TraceAggregator::StopRequested() const noexcept {
  return stop_requested_.load(std::memory_order_relaxed);
}

Trace TraceAggregator::CreateProcessDescriptorPacket() const {
  Trace trace;
  auto* packet = trace.add_packet();

  auto* process_track_descriptor = new TrackDescriptor();
  process_track_descriptor->set_uuid(process_track_uuid_);

  auto* process_descriptor = new ProcessDescriptor();
  process_descriptor->set_pid(getpid());
  process_descriptor->set_process_name(config_.process_name);

  process_track_descriptor->set_allocated_process(process_descriptor);
  packet->set_allocated_track_descriptor(process_track_descriptor);

  return trace;
}

Trace TraceAggregator::CreateThreadDescriptorPacket(const ThreadTracer& thread_tracer) const {
  Trace trace;

  auto* packet = trace.add_packet();

  auto* thread_track_descriptor = new TrackDescriptor();
  thread_track_descriptor->set_uuid(thread_tracer.track_uuid_);
  thread_track_descriptor->set_parent_uuid(process_track_uuid_);

  auto* thread_descriptor = new ThreadDescriptor();
  thread_descriptor->set_pid(getpid());
  thread_descriptor->set_tid(thread_tracer.tid_);
  thread_descriptor->set_thread_name(thread_tracer.name_);

  thread_track_descriptor->set_allocated_thread(thread_descriptor);
  packet->set_allocated_track_descriptor(thread_track_descriptor);

  return trace;
}

void TraceAggregator::AddTrackEventPacketToTrace(
  Trace&                    trace,
  const ThreadTracer&       thread_tracer,
  const TrackEventInternal& track_event_internal
) const {
  auto* packet = trace.add_packet();
  packet->set_timestamp(track_event_internal.timestamp);

  auto* track_event = new TrackEvent();
  track_event->set_track_uuid(thread_tracer.track_uuid_);
  track_event->set_type(track_event_internal.type);

  if (track_event_internal.name != nullptr) {
    track_event->set_name(track_event_internal.name);
  }

  // TODO: set category
  // Trickier to do because this needs to allocate an array and stuff
  // if (track_event.category != nullptr) {
  //   track_event_proto->set_categories(track_event.category);
  // }

  packet->set_allocated_track_event(track_event);
  packet->set_trusted_packet_sequence_id(thread_tracer.trusted_packet_sequence_id_);
}

}  // namespace cactus_rt::tracing
