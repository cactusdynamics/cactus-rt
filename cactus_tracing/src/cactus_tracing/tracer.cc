#include "cactus_tracing/tracer.h"

#include <unistd.h>

#include "trace.pb.h"

using cactus_tracing::vendor::perfetto::protos::ProcessDescriptor;
using cactus_tracing::vendor::perfetto::protos::ThreadDescriptor;
using cactus_tracing::vendor::perfetto::protos::Trace;
using cactus_tracing::vendor::perfetto::protos::TrackDescriptor;
using cactus_tracing::vendor::perfetto::protos::TrackEvent_Type_TYPE_INSTANT;
using cactus_tracing::vendor::perfetto::protos::TrackEvent_Type_TYPE_SLICE_BEGIN;
using cactus_tracing::vendor::perfetto::protos::TrackEvent_Type_TYPE_SLICE_END;
using TrackEventProto = cactus_tracing::vendor::perfetto::protos::TrackEvent;

using namespace std::chrono_literals;

namespace cactus_tracing {
Tracer::Tracer(const char* process_name, const char* output_filename)
    : process_name_(process_name),
      output_filename_(output_filename),
      output_file_(output_filename, std::ios::out | std::ios::trunc | std::ios::binary) {
  process_pid_ = getpid();

  // TODO: Should this be a real uuid or is this restricted use case of
  // perfetto OK with the just the pid?
  process_uuid_ = static_cast<uint64_t>(process_pid_);
}

void Tracer::StartBackgroundThread() {
  std::thread background_thread{
    [this]() {
      // TODO: set CPU affinity
      this->BackgroundThreadMain();
    }};

  // Move the ownership to the member variable so we don't lose it
  background_thread_.swap(background_thread);
}

void Tracer::StopBackgroundThread() {
  stop_requested_.store(true, std::memory_order_relaxed);
}

void Tracer::JoinBackgroundThread() {
  background_thread_.join();
}

void Tracer::RegisterThreadTracer(std::shared_ptr<ThreadTracer> thread_tracer) {
  const std::scoped_lock lock(mutex_);

  thread_tracers_.push_back(thread_tracer);
  thread_descriptor_trace_packets_.push_back(CreateThreadDescriptorPacket(*thread_tracer));
}

void Tracer::BackgroundThreadMain() {
  // Emit this first event before emitting any other events for the process
  bool success = WriteProcessDescriptorPacket();
  if (!success) {
    // TODO: deal with this
    return;
  }

  {
    const std::scoped_lock lock(mutex_);
    EmptyTrackDescriptorPackets();
  }

  while (!stop_requested_.load(std::memory_order_relaxed)) {
    // The lock is for accessing the thread_tracers_ variable only, as we can
    // RegisterThreadTracer at any point in the program.
    // TODO: investigate not needing this.
    const std::scoped_lock lock(mutex_);

    // In case anything registered, we need to write the track descriptor packet first.
    EmptyTrackDescriptorPackets();

    int tracers_with_events = 0;

    for (const auto& thread_tracer : thread_tracers_) {
      TrackEvent event;
      if (!thread_tracer->queue_.try_dequeue(event)) {
        continue;
      }

      tracers_with_events++;
      const auto trace = CreateTrackEventPacket(event, *thread_tracer);
      WriteTrace(trace);  // TODO: handle failure
    }

    // TODO: check for dropped messages

    if (tracers_with_events == 0) {
      std::this_thread::sleep_for(10ms);
    }
  }

  while (true) {
    int tracers_with_events = 0;

    for (const auto& thread_tracer : thread_tracers_) {
      TrackEvent event;
      if (!thread_tracer->queue_.try_dequeue(event)) {
        continue;
      }

      tracers_with_events++;

      const auto trace = CreateTrackEventPacket(event, *thread_tracer);
      WriteTrace(trace);  // TODO: handle failure
    }

    if (tracers_with_events == 0) {
      break;  // empty. so quit
    }
  }
}

// TOOD: make it clear this is not thread safe.
bool Tracer::EmptyTrackDescriptorPackets() {
  for (const auto& trace : thread_descriptor_trace_packets_) {
    if (!WriteTrace(trace)) {
      return false;  // TODO: this is more severe. Need to log it somehow?
    }
  }

  thread_descriptor_trace_packets_.clear();
  return true;
}

bool Tracer::WriteTrace(const Trace& trace) {
  return trace.SerializeToOstream(&output_file_);
}

// TODO: refactor this into Create... and WriteTrace
bool Tracer::WriteProcessDescriptorPacket() {
  Trace trace;
  auto* packet = trace.add_packet();

  auto* process_track_descriptor = new TrackDescriptor();
  process_track_descriptor->set_uuid(process_uuid_);

  auto* process_descriptor = new ProcessDescriptor();
  process_descriptor->set_pid(process_pid_);
  process_descriptor->set_process_name(process_name_);

  // set_* will transfer the ownership of the raw pointer to
  // process_track_descriptor so we don't need to worry about freeing it.
  process_track_descriptor->set_allocated_process(process_descriptor);
  packet->set_allocated_track_descriptor(process_track_descriptor);

  return trace.SerializeToOstream(&output_file_);
}

Trace Tracer::CreateThreadDescriptorPacket(const ThreadTracer& thread_tracer) const {
  Trace trace;
  auto* packet = trace.add_packet();

  auto* thread_track_descriptor = new TrackDescriptor();
  thread_track_descriptor->set_uuid(thread_tracer.thread_uuid_);
  thread_track_descriptor->set_parent_uuid(process_uuid_);

  auto* thread_descriptor = new ThreadDescriptor();
  thread_descriptor->set_pid(process_pid_);
  thread_descriptor->set_tid(thread_tracer.thread_tid_);
  thread_descriptor->set_thread_name(thread_tracer.thread_name_);

  thread_track_descriptor->set_allocated_thread(thread_descriptor);
  packet->set_allocated_track_descriptor(thread_track_descriptor);

  return trace;
}

Trace Tracer::CreateTrackEventPacket(const TrackEvent& track_event, const ThreadTracer& thread_tracer) const {
  Trace trace;
  auto* packet = trace.add_packet();
  packet->set_timestamp(track_event.timestamp);

  auto* track_event_proto = new TrackEventProto();
  track_event_proto->set_track_uuid(thread_tracer.thread_uuid_);

  // TODO: make this conversion better...
  switch (track_event.type) {
    case TrackEvent::Type::SLICE_BEGIN:
      track_event_proto->set_type(TrackEvent_Type_TYPE_SLICE_BEGIN);
      break;
    case TrackEvent::Type::SLICE_END:
      track_event_proto->set_type(TrackEvent_Type_TYPE_SLICE_END);
      break;
    case TrackEvent::Type::INSTANT:
      track_event_proto->set_type(TrackEvent_Type_TYPE_INSTANT);
      break;
    default:
      track_event_proto->set_type(vendor::perfetto::protos::TrackEvent_Type_TYPE_UNSPECIFIED);
  }

  if (track_event.name != nullptr) {
    track_event_proto->set_name(track_event.name);
  }

  // TODO: set category
  // if (track_event.category != nullptr) {
  //   track_event_proto->set_categories(track_event.category);
  // }

  // TODO: set counter_value

  packet->set_allocated_track_event(track_event_proto);
  packet->set_trusted_packet_sequence_id(thread_tracer.trusted_packet_sequence_id_);

  return trace;
}

}  // namespace cactus_tracing
