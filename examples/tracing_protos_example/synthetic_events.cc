#include <google/protobuf/util/delimited_message_util.h>

#include <cstdint>
#include <fstream>

#include "trace.pb.h"

using cactus_tracing::vendor::perfetto::protos::InternedData;
using cactus_tracing::vendor::perfetto::protos::ProcessDescriptor;
using cactus_tracing::vendor::perfetto::protos::ThreadDescriptor;
using cactus_tracing::vendor::perfetto::protos::Trace;
using cactus_tracing::vendor::perfetto::protos::TracePacket_SequenceFlags_SEQ_INCREMENTAL_STATE_CLEARED;
using cactus_tracing::vendor::perfetto::protos::TracePacket_SequenceFlags_SEQ_NEEDS_INCREMENTAL_STATE;
using cactus_tracing::vendor::perfetto::protos::TrackDescriptor;
using cactus_tracing::vendor::perfetto::protos::TrackEvent;
using cactus_tracing::vendor::perfetto::protos::TrackEvent_Type_TYPE_INSTANT;
using cactus_tracing::vendor::perfetto::protos::TrackEvent_Type_TYPE_SLICE_BEGIN;
using cactus_tracing::vendor::perfetto::protos::TrackEvent_Type_TYPE_SLICE_END;

int main() {
  // Verify that the version of the library that we linked against is
  // compatible with the version of the headers we compiled against.
  GOOGLE_PROTOBUF_VERIFY_VERSION;

  // This will create a trace that follows the example here: https://perfetto.dev/docs/reference/synthetic-track-event#thread-scoped-sync-slices

  constexpr uint64_t process_uuid = 894893984;
  constexpr uint64_t thread_uuid = 49083589894;
  constexpr uint64_t process_pid = 1234;
  constexpr uint64_t thread_tid = 5678;

  // This should be per-thread. See https://github.com/google/perfetto/issues/124
  constexpr uint64_t trusted_packet_sequence_id = 3903809;

  // Emit this packet once *before* you emit the first event for this process.
  Trace trace1;
  auto* packet1 = trace1.add_packet();
  auto* process_track_descriptor = new TrackDescriptor();
  process_track_descriptor->set_uuid(process_uuid);

  auto* process_descriptor = new ProcessDescriptor();
  process_descriptor->set_pid(process_pid);
  process_descriptor->set_process_name("My process name");

  // This transfers the ownership of process_descriptor to track_descriptor1.
  // As long as we don't call track_descriptor1->release_thread(),
  // track_descriptor_1 will delete the process_descriptor memory when freed.
  process_track_descriptor->set_allocated_process(process_descriptor);
  // NOLINTNEXTLINE(clang-analyzer-cplusplus.NewDeleteLeaks)
  packet1->set_allocated_track_descriptor(process_track_descriptor);

  // Emit this packet once *before* you emit the first event for this thread.
  Trace trace2;
  auto* packet2 = trace2.add_packet();

  auto* thread_track_descriptor = new TrackDescriptor();
  thread_track_descriptor->set_uuid(thread_uuid);
  thread_track_descriptor->set_parent_uuid(process_uuid);

  auto* thread_descriptor = new ThreadDescriptor();
  thread_descriptor->set_pid(process_pid);
  thread_descriptor->set_tid(thread_tid);
  thread_descriptor->set_thread_name("My thread name");

  // NOLINTNEXTLINE(clang-analyzer-cplusplus.NewDeleteLeaks)
  thread_track_descriptor->set_allocated_thread(thread_descriptor);
  // NOLINTNEXTLINE(clang-analyzer-cplusplus.NewDeleteLeaks)
  packet2->set_allocated_track_descriptor(thread_track_descriptor);

  // The events for this thread.
  Trace trace3;
  auto* packet3 = trace3.add_packet();
  packet3->set_timestamp(200);

  auto* interned_data1 = new InternedData();
  auto* event_name = interned_data1->add_event_names();
  event_name->set_iid(1);
  event_name->set_name("My special parent");
  packet3->set_allocated_interned_data(interned_data1);

  auto* track_event1 = new TrackEvent();
  track_event1->set_type(TrackEvent_Type_TYPE_SLICE_BEGIN);
  track_event1->set_track_uuid(thread_uuid);
  track_event1->set_name_iid(1);
  packet3->set_allocated_track_event(track_event1);

  packet3->set_trusted_packet_sequence_id(trusted_packet_sequence_id);
  packet3->set_previous_packet_dropped(true);
  packet3->set_first_packet_on_sequence(true);
  packet3->set_sequence_flags(TracePacket_SequenceFlags_SEQ_INCREMENTAL_STATE_CLEARED | TracePacket_SequenceFlags_SEQ_NEEDS_INCREMENTAL_STATE);

  Trace trace4;
  auto* packet4 = trace4.add_packet();
  packet4->set_timestamp(250);

  auto* track_event2 = new TrackEvent();
  track_event2->set_type(TrackEvent_Type_TYPE_SLICE_BEGIN);
  track_event2->set_track_uuid(thread_uuid);
  track_event2->set_name("My special child");
  packet4->set_allocated_track_event(track_event2);

  packet4->set_trusted_packet_sequence_id(trusted_packet_sequence_id);

  Trace trace5;
  auto* packet5 = trace5.add_packet();
  packet5->set_timestamp(285);

  auto* track_event3 = new TrackEvent();
  track_event3->set_name("My special marker!");
  track_event3->set_type(TrackEvent_Type_TYPE_INSTANT);
  track_event3->set_track_uuid(thread_uuid);
  packet5->set_allocated_track_event(track_event3);

  packet5->set_trusted_packet_sequence_id(trusted_packet_sequence_id);

  Trace trace6;
  auto* packet6 = trace6.add_packet();
  packet6->set_timestamp(290);

  auto* track_event4 = new TrackEvent();
  track_event4->set_type(TrackEvent_Type_TYPE_SLICE_END);
  track_event4->set_track_uuid(thread_uuid);
  packet6->set_allocated_track_event(track_event4);

  packet6->set_trusted_packet_sequence_id(trusted_packet_sequence_id);

  Trace trace7;
  auto* packet7 = trace7.add_packet();
  packet7->set_timestamp(300);

  auto* track_event5 = new TrackEvent();
  track_event5->set_type(TrackEvent_Type_TYPE_SLICE_END);
  track_event5->set_track_uuid(thread_uuid);
  packet7->set_allocated_track_event(track_event5);

  packet7->set_trusted_packet_sequence_id(trusted_packet_sequence_id);

  Trace trace8;
  auto* packet8 = trace8.add_packet();
  packet8->set_timestamp(350);

  auto* track_event8 = new TrackEvent();
  track_event8->set_type(TrackEvent_Type_TYPE_SLICE_BEGIN);
  track_event8->set_track_uuid(thread_uuid);
  track_event8->set_name_iid(1);
  packet8->set_allocated_track_event(track_event8);
  packet8->set_sequence_flags(TracePacket_SequenceFlags_SEQ_NEEDS_INCREMENTAL_STATE);

  packet8->set_trusted_packet_sequence_id(trusted_packet_sequence_id);

  Trace trace9;
  auto* packet9 = trace9.add_packet();
  packet9->set_timestamp(500);

  auto* track_event9 = new TrackEvent();
  track_event9->set_type(TrackEvent_Type_TYPE_SLICE_END);
  track_event9->set_track_uuid(thread_uuid);
  packet9->set_allocated_track_event(track_event9);

  packet9->set_trusted_packet_sequence_id(trusted_packet_sequence_id);

  {
    std::fstream output("build/direct_proto_serialization.perfetto-trace", std::ios::out | std::ios::trunc | std::ios::binary);

    const std::array<Trace*, 9> traces{
      &trace1,
      &trace2,
      &trace3,
      &trace4,
      &trace5,
      &trace6,
      &trace7,
      &trace8,
      &trace9,
    };

    for (const auto* trace : traces) {
      trace->SerializeToOstream(&output);
    }
  }

  google::protobuf::ShutdownProtobufLibrary();

  return 0;
}
