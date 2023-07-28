#include "cactus_rt/tracing/tracer.h"

#include <unistd.h>

#include <chrono>
#include <thread>

#include "cactus_rt/utils.h"

using Trace = cactus_tracing::vendor::perfetto::protos::Trace;
using TrackDescriptor = cactus_tracing::vendor::perfetto::protos::TrackDescriptor;
using ThreadDescriptor = cactus_tracing::vendor::perfetto::protos::ThreadDescriptor;
using ProcessDescriptor = cactus_tracing::vendor::perfetto::protos::ProcessDescriptor;
using TrackEvent = cactus_tracing::vendor::perfetto::protos::TrackEvent;

using namespace std::chrono_literals;

namespace cactus_rt::tracing {
Tracer::Tracer(const char* process_name, std::vector<size_t> cpu_affinity)
    : process_name_(process_name),
      process_pid_(getpid()),
      // TODO: Should this be a real uuid or is this restricted use case of
      // perfetto OK with the just the pid?
      process_track_uuid_(static_cast<uint64_t>(process_pid_)) {
  // The process always needs one of these.
  this->sticky_trace_packets_.push_back(CreateProcessDescriptorPacket());
}

ThreadTracer& Tracer::CreateThreadTracer(const char* thread_name, uint32_t queue_capacity) {
  // Can only create new thread tracers when not writing metrics to sinks.
  const std::scoped_lock lock(mutex_);

  // Atomically (as we are protected by the above lock) generate thread_track_uuid and trusted_packet_sequence_id
  static uint64_t thread_track_uuid = 1000;
  static uint32_t trusted_packet_sequence_id = 1000;
  thread_track_uuid++;
  trusted_packet_sequence_id++;

  // Create and register the thread tracer
  auto& thread_tracer = thread_tracers_.emplace_back(
    *this,
    thread_name,
    GetThreadId(),
    thread_track_uuid,
    trusted_packet_sequence_id,
    queue_capacity
  );

  // Create thread track descriptors and write it to all existing sinks.
  auto trace = CreateThreadDescriptorPacket(thread_tracer);

  for (auto& sink : sinks_) {
    // TODO: deal with errors
    sink->Write(trace);
  }

  // Move the trace packet to the sticky packets so newly registered sinks gets
  // this packet when they get registered.
  this->sticky_trace_packets_.push_back(std::move(trace));

  return thread_tracer;
}

void Tracer::RegisterSink(std::unique_ptr<Sink> sink) {
  // Can only create new sinks when not writing metrics to sinks. This is so we
  // don't lose any packets or have track event packets appear before the
  // descriptors packets.
  const std::scoped_lock lock(mutex_);

  for (const auto& trace : this->sticky_trace_packets_) {
    // TODO: deal with errors
    sink->Write(trace);
  }

  sinks_.push_back(std::move(sink));
}

void Tracer::Run() {
  while (!StopRequested()) {
    // This lock is needed as when we are writing packets into sinks, we don't
    // want new thread tracers and sinks to be created or registered as that
    // can cause potential data loss. This lock is NOT for dequeueing from the
    // thread tracer queues, as expected.
    const std::scoped_lock lock(mutex_);

    int   tracers_with_events = 0;
    Trace trace;

    for (auto& thread_tracer : thread_tracers_) {
      TrackEventInternal event;
      if (!thread_tracer.queue_.try_dequeue(event)) {
        // No event in this queue.
        continue;
      }

      tracers_with_events++;
      AddTrackEventPacketToTrace(trace, thread_tracer, event);
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

    for (auto& thread_tracer : thread_tracers_) {
      TrackEventInternal event;
      if (!thread_tracer.queue_.try_dequeue(event)) {
        continue;
      }

      tracers_with_events++;
      AddTrackEventPacketToTrace(trace, thread_tracer, event);
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

Trace Tracer::CreateProcessDescriptorPacket() const {
  Trace trace;
  auto* packet = trace.add_packet();

  auto* process_track_descriptor = new TrackDescriptor();
  process_track_descriptor->set_uuid(process_track_uuid_);

  auto* process_descriptor = new ProcessDescriptor();
  process_descriptor->set_pid(process_pid_);
  process_descriptor->set_process_name(process_name_);

  process_track_descriptor->set_allocated_process(process_descriptor);
  packet->set_allocated_track_descriptor(process_track_descriptor);

  return trace;
}

Trace Tracer::CreateThreadDescriptorPacket(const ThreadTracer& thread_tracer) const {
  Trace trace;

  auto* packet = trace.add_packet();

  auto* thread_track_descriptor = new TrackDescriptor();
  thread_track_descriptor->set_uuid(thread_tracer.thread_track_uuid_);
  thread_track_descriptor->set_parent_uuid(process_track_uuid_);

  auto* thread_descriptor = new ThreadDescriptor();
  thread_descriptor->set_pid(process_pid_);
  thread_descriptor->set_tid(thread_tracer.thread_tid_);
  thread_descriptor->set_thread_name(thread_tracer.thread_name_);

  thread_track_descriptor->set_allocated_thread(thread_descriptor);
  packet->set_allocated_track_descriptor(thread_track_descriptor);

  return trace;
}

void Tracer::AddTrackEventPacketToTrace(
  Trace&                    trace,
  const ThreadTracer&       thread_tracer,
  const TrackEventInternal& track_event_internal
) const {
  auto* packet = trace.add_packet();
  packet->set_timestamp(track_event_internal.timestamp);

  auto* track_event = new TrackEvent();
  track_event->set_track_uuid(thread_tracer.thread_track_uuid_);
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
