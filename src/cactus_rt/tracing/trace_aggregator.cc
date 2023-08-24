#include "cactus_rt/tracing/trace_aggregator.h"

#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif

#include <pthread.h>
#include <sched.h>

#include <chrono>
#include <cstring>
#include <string>

using Trace = cactus_tracing::vendor::perfetto::protos::Trace;
using TrackDescriptor = cactus_tracing::vendor::perfetto::protos::TrackDescriptor;
using ThreadDescriptor = cactus_tracing::vendor::perfetto::protos::ThreadDescriptor;
using ProcessDescriptor = cactus_tracing::vendor::perfetto::protos::ProcessDescriptor;
using TrackEvent = cactus_tracing::vendor::perfetto::protos::TrackEvent;

using namespace std::chrono_literals;

namespace cactus_rt::tracing {
TraceAggregator::TraceAggregator(const char* process_name, std::vector<size_t> cpu_affinity)
    : process_name_(process_name),
      cpu_affinity_(cpu_affinity),
      process_track_uuid_(static_cast<uint64_t>(getpid())),
      logger_(quill::create_logger("__trace_aggregator__")) {
  this->sticky_trace_packets_.push_back(CreateProcessDescriptorPacket());
}

void TraceAggregator::RegisterSink(std::shared_ptr<Sink> sink) {
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

  sinks_.push_back(sink);
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

void TraceAggregator::DeregisterThreadTracer(const std::shared_ptr<ThreadTracer>& tracer) {
  const std::scoped_lock lock(mutex_);

  tracers_.remove_if([tracer](const std::shared_ptr<tracing::ThreadTracer>& t) {
    return t == tracer;
  });
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
  SetupCPUAffinityIfNecessary();

  while (!StopRequested()) {
    uint32_t events_written = 0;
    {
      const std::scoped_lock lock(mutex_);
      Trace                  trace;
      events_written = DequeueSingleEventForEachTracer(trace);
      if (events_written > 0) {
        // TODO: error handling
        WriteTraceToAllSinks(trace);
      }
    }

    if (events_written == 0) {
      // No events from any tracers. We can let the TraceAggregator sleep and
      // save some power while the queues accumulate some messages.
      //
      // TODO: this sleep duration should be customizable.
      // The sleep duration + the queue size determines the maximum theoretical
      // message rate.
      std::this_thread::sleep_for(10ms);
    }

    // TODO: check if there are any dropped messages and log a warning?
  }

  DrainTraceEvents();
}

uint32_t TraceAggregator::DequeueSingleEventForEachTracer(Trace& trace) {
  uint32_t events = 0;
  for (auto& tracer : tracers_) {
    TrackEventInternal event;
    if (!tracer->queue_.try_dequeue(event)) {
      // No event for this tracer
      continue;
    }

    events++;
    AddTrackEventPacketToTrace(trace, *tracer, event);
  }

  return events;
}

bool TraceAggregator::WriteTraceToAllSinks(const Trace& trace) {
  bool success = true;

  // TODO: better error handling? Right now it's a best effort write to all sinks.
  for (auto& sink : sinks_) {
    if (!sink->Write(trace)) {
      success = false;
    }
  }

  return success;
}

uint64_t TraceAggregator::DrainTraceEvents() {
  Trace    trace;
  uint64_t total_events = 0;

  while (true) {
    auto events = DequeueSingleEventForEachTracer(trace);
    if (events == 0) {
      break;
    }

    total_events += events;
  }

  if (total_events > 0) {
    // TODO: error handling
    WriteTraceToAllSinks(trace);
  }

  return total_events;
}

bool TraceAggregator::StopRequested() const noexcept {
  return stop_requested_.load(std::memory_order_relaxed);
}

void TraceAggregator::SetupCPUAffinityIfNecessary() const {
  if (cpu_affinity_.empty()) {
    return;
  }

  cpu_set_t cpuset;
  CPU_ZERO(&cpuset);
  for (auto cpu : cpu_affinity_) {
    CPU_SET(cpu, &cpuset);
  }

  const int ret = pthread_setaffinity_np(pthread_self(), sizeof(cpu_set_t), &cpuset);
  if (ret == 0) {
    return;
  }

  throw std::runtime_error{std::string("cannot set affinity for trace aggregator: ") + std::strerror(errno)};
}

Trace TraceAggregator::CreateProcessDescriptorPacket() const {
  // NOLINTBEGIN(clang-analyzer-cplusplus.NewDeleteLeaks)
  Trace trace;
  auto* packet = trace.add_packet();

  auto* process_track_descriptor = new TrackDescriptor();
  process_track_descriptor->set_uuid(process_track_uuid_);

  auto* process_descriptor = new ProcessDescriptor();
  process_descriptor->set_pid(getpid());
  process_descriptor->set_process_name(process_name_);

  process_track_descriptor->set_allocated_process(process_descriptor);
  packet->set_allocated_track_descriptor(process_track_descriptor);
  // NOLINTEND(clang-analyzer-cplusplus.NewDeleteLeaks)

  return trace;
}

Trace TraceAggregator::CreateThreadDescriptorPacket(const ThreadTracer& thread_tracer) const {
  // NOLINTBEGIN(clang-analyzer-cplusplus.NewDeleteLeaks)
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
  // NOLINTEND(clang-analyzer-cplusplus.NewDeleteLeaks)

  return trace;
}

void TraceAggregator::AddTrackEventPacketToTrace(
  Trace&                    trace,
  const ThreadTracer&       thread_tracer,
  const TrackEventInternal& track_event_internal
) const {
  // NOLINTBEGIN(clang-analyzer-cplusplus.NewDeleteLeaks)
  auto* packet = trace.add_packet();
  packet->set_timestamp(track_event_internal.timestamp);

  auto* track_event = new TrackEvent();
  track_event->set_track_uuid(thread_tracer.track_uuid_);
  track_event->set_type(track_event_internal.type);

  if (track_event_internal.name != nullptr) {
    track_event->set_name(track_event_internal.name);
  }

  // TODO: support multiple categories later?
  if (track_event_internal.category != nullptr) {
    track_event->add_categories(track_event_internal.category);
  }

  packet->set_allocated_track_event(track_event);
  packet->set_trusted_packet_sequence_id(thread_tracer.trusted_packet_sequence_id_);
  // NOLINTEND(clang-analyzer-cplusplus.NewDeleteLeaks)
}

}  // namespace cactus_rt::tracing
