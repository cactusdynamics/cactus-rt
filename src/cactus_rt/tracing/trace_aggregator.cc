#include "cactus_rt/tracing/trace_aggregator.h"

#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif

#include <pthread.h>
#include <sched.h>

#include <chrono>
#include <cstring>
#include <string>

using cactus_tracing::vendor::perfetto::protos::ProcessDescriptor;
using cactus_tracing::vendor::perfetto::protos::ThreadDescriptor;
using cactus_tracing::vendor::perfetto::protos::Trace;
using cactus_tracing::vendor::perfetto::protos::TracePacket;
using cactus_tracing::vendor::perfetto::protos::TracePacket_SequenceFlags_SEQ_INCREMENTAL_STATE_CLEARED;
using cactus_tracing::vendor::perfetto::protos::TracePacket_SequenceFlags_SEQ_NEEDS_INCREMENTAL_STATE;
using cactus_tracing::vendor::perfetto::protos::TrackDescriptor;
using cactus_tracing::vendor::perfetto::protos::TrackEvent;

using namespace std::chrono_literals;

namespace {
constexpr size_t kMaxInternedStrings = 10000;
}

namespace cactus_rt::tracing {
TraceAggregator::TraceAggregator(std::string process_name, std::vector<size_t> cpu_affinity)
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

  auto interned_data_trace = CreateInitialInternedDataPacket();
  if (interned_data_trace) {
    // TODO: deal with errors
    sink->Write(*interned_data_trace);
  }

  sinks_.push_back(sink);
}

void TraceAggregator::RegisterThreadTracer(std::shared_ptr<ThreadTracer> tracer) {
  if (tracer->tid_ == 0) {
    LOG_WARNING(Logger(), "thread {} does not have a valid tid", tracer->name_);
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
    return t.get() == tracer.get();
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
    Trace trace;
    auto  num_events = TryDequeueOnceFromAllTracers(trace);

    // TODO: Instead of writing the trace directly, we should put it into a
    // bigger memory queue (bigger than the tracer queue), which would be
    // written out in another thread. That should reduce the bottlenecks for
    // this loop as otherwise this loop would be blocked by the writer.

    if (num_events > 0) {
      WriteTrace(trace);
    } else {
      // No events from any tracers! We can sleep and let the queues accumulate a bit.
      // TODO: customize this sleep period
      std::this_thread::sleep_for(10ms);
    }
  }

  // When the trace aggregator is requested to stop, there may still be some
  // packets in the tracer queues. We aim to write out as much as possible.
  // TODO: right now we accumulate a giant Trace message and write it all
  // together. In the future there should be batch writing, which may be more
  // efficient.
  Trace  trace;
  size_t total_events = 0;
  while (true) {
    auto num_events = TryDequeueOnceFromAllTracers(trace);
    total_events += num_events;

    // This is a busy loop that pops from the queues. As soon as there are no
    // more events being emitted, it quits. If the queues are being further
    // written to, the data would be lost and it is likely OK.
    //
    // TODO: have a timeout that guarantees the trace aggregator will stop after X seconds.
    if (num_events == 0) {
      break;
    }
  }

  if (total_events > 0) {
    WriteTrace(trace);
  }
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

size_t TraceAggregator::TryDequeueOnceFromAllTracers(Trace& trace) noexcept {
  // This lock is needed because we are accessing the tracer_, which can race
  // with other threads that are registering a thread tracer. This is NOT for
  // dequeuing from the thread_tracer queues.
  const std::scoped_lock lock(mutex_);
  size_t                 num_events = 0;

  for (auto& tracer : tracers_) {
    TrackEventInternal event;
    if (!tracer->queue_.try_dequeue(event)) {
      // No event in this queue.
      continue;
    }

    // TODO: While the dequeue is happening, we should check each tracer for
    // errors/full queue problems.

    num_events++;
    AddTrackEventPacketToTrace(trace, *tracer, event);
  }

  return num_events;
}

void TraceAggregator::WriteTrace(const Trace& trace) noexcept {
  // This lock is needed because we are accessing the sinks_, which can race
  // with other threads that are registering a sink. This is NOT for dequeuing
  // from the thread_tracer queues.
  const std::scoped_lock lock(mutex_);

  // TODO: better handle error by maybe emitting an error signal and calling an error callback?
  for (auto& sink : sinks_) {
    if (!sink->Write(trace)) {
      LOG_WARNING_LIMIT(std::chrono::milliseconds(5000), Logger(), "failed to write trace data to sink, data may be corrupted");
    }
  }
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
  thread_descriptor->set_thread_name(thread_tracer.name_.c_str());

  thread_track_descriptor->set_allocated_thread(thread_descriptor);
  packet->set_allocated_track_descriptor(thread_track_descriptor);
  // NOLINTEND(clang-analyzer-cplusplus.NewDeleteLeaks)

  return trace;
}

void TraceAggregator::AddTrackEventPacketToTrace(
  Trace&                    trace,
  ThreadTracer&             thread_tracer,
  const TrackEventInternal& track_event_internal
) {
  // NOLINTBEGIN(clang-analyzer-cplusplus.NewDeleteLeaks)
  uint32_t      sequence_flags = 0;
  InternedData* interned_data = nullptr;

  // Create trace packet
  auto* packet = trace.add_packet();
  packet->set_timestamp(track_event_internal.timestamp);

  // Create track event
  auto* track_event = new TrackEvent();
  track_event->set_track_uuid(thread_tracer.track_uuid_);
  track_event->set_type(track_event_internal.type);

  // Deal with the event name
  if (track_event_internal.name != nullptr) {
    if (thread_tracer.event_name_interner_.Size() < kMaxInternedStrings) {
      auto [new_event_name, event_name_iid] = thread_tracer.event_name_interner_.GetId(track_event_internal.name);

      // If this is a never-seen-before event name, we need to emit the interned data into the data stream.
      if (new_event_name) {
        if (interned_data == nullptr) {
          interned_data = new InternedData();
        }

        auto* event_name = interned_data->add_event_names();
        event_name->set_iid(event_name_iid);
        event_name->set_name(track_event_internal.name);
      }

      // Finally set the name_iid
      track_event->set_name_iid(event_name_iid);
      sequence_flags |= TracePacket_SequenceFlags_SEQ_NEEDS_INCREMENTAL_STATE;
    } else {
      LOG_WARNING_LIMIT(
        std::chrono::milliseconds(5000),
        Logger(),
        "number of unique event names emitted in tracing is exceeding {} for thread {}, string interning is disabled. trace files may be excessively large",
        kMaxInternedStrings,
        thread_tracer.name_
      );
      track_event->set_name(track_event_internal.name);
    }
  }
  // Deal with the event category. Code is slightly duplicated, which is fine
  // for readability as we only have name and category to intern.
  // TODO: support multiple categories later?
  if (track_event_internal.category != nullptr) {
    if (thread_tracer.event_category_interner_.Size() < kMaxInternedStrings) {
      auto [new_category, category_iid] = thread_tracer.event_category_interner_.GetId(track_event_internal.category);

      // If this is a never-seen-before event category, we need to emit the interned data into the data stream.
      if (new_category) {
        if (interned_data == nullptr) {
          interned_data = new InternedData();
        }

        auto* category = interned_data->add_event_categories();
        category->set_iid(category_iid);
        category->set_name(track_event_internal.category);
      }

      // Finally set the category
      track_event->add_category_iids(category_iid);
      sequence_flags |= TracePacket_SequenceFlags_SEQ_NEEDS_INCREMENTAL_STATE;
    } else {
      LOG_WARNING_LIMIT(
        std::chrono::milliseconds(5000),
        Logger(),
        "number of unique event category emitted in tracing is exceeding {} for thread {}, string interning is disabled. trace files may be excessively large",
        kMaxInternedStrings,
        thread_tracer.name_
      );
      track_event->add_categories(track_event_internal.category);
    }
  }

  // Set the track event into the packet and setup packet sequence id
  packet->set_allocated_track_event(track_event);
  packet->set_trusted_packet_sequence_id(thread_tracer.trusted_packet_sequence_id_);

  // Deal with "first packet"
  if (sequences_with_first_packet_emitted_.count(thread_tracer.trusted_packet_sequence_id_) == 0) {
    sequences_with_first_packet_emitted_.insert(thread_tracer.trusted_packet_sequence_id_);

    packet->set_first_packet_on_sequence(true);
    packet->set_previous_packet_dropped(true);
    sequence_flags |= TracePacket_SequenceFlags_SEQ_INCREMENTAL_STATE_CLEARED;
  }

  // If interned data exists, add it to the packet
  if (interned_data != nullptr) {
    packet->set_allocated_interned_data(interned_data);
  }

  // Write the sequence flag is needed
  if (sequence_flags != 0) {
    packet->set_sequence_flags(sequence_flags);
  }
  // NOLINTEND(clang-analyzer-cplusplus.NewDeleteLeaks)
}

std::optional<Trace> TraceAggregator::CreateInitialInternedDataPacket() const {
  Trace trace;

  bool wrote_interned_data = false;

  for (const auto& tracer : this->tracers_) {
    InternedData* interned_data = nullptr;
    for (const auto& [name, name_iid] : tracer->event_name_interner_.Ids()) {
      if (interned_data == nullptr) {
        interned_data = new InternedData();
      }

      auto* event_name = interned_data->add_event_names();
      event_name->set_name(name.data());
      event_name->set_iid(name_iid);
    }

    for (const auto& [category, category_iid] : tracer->event_category_interner_.Ids()) {
      if (interned_data == nullptr) {
        interned_data = new InternedData();
      }

      auto* event_category = interned_data->add_event_categories();
      event_category->set_name(category.data());
      event_category->set_iid(category_iid);
    }

    if (interned_data != nullptr) {
      wrote_interned_data = true;
      TracePacket* packet = trace.add_packet();

      // TODO: is it okay to not have a timestamp?
      // packet->set_timestamp(initial_timestamp);

      packet->set_allocated_interned_data(interned_data);
      packet->set_trusted_packet_sequence_id(tracer->trusted_packet_sequence_id_);
    }
  }

  if (wrote_interned_data) {
    return trace;
  }

  return std::nullopt;
}

}  // namespace cactus_rt::tracing
