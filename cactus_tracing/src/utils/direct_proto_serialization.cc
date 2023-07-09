#include <google/protobuf/util/delimited_message_util.h>

#include <cstdint>
#include <fstream>

#include "trace.pb.h"

using cactus_tracing::vendor::perfetto::protos::ProcessDescriptor;
using cactus_tracing::vendor::perfetto::protos::ThreadDescriptor;
using cactus_tracing::vendor::perfetto::protos::Trace;
using cactus_tracing::vendor::perfetto::protos::TracePacket;
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

  thread_track_descriptor->set_allocated_thread(thread_descriptor);
  packet2->set_allocated_track_descriptor(thread_track_descriptor);

  // The events for this thread.
  Trace trace3;
  auto* packet3 = trace3.add_packet();
  packet3->set_timestamp(200);

  auto* track_event1 = new TrackEvent();
  track_event1->set_type(TrackEvent_Type_TYPE_SLICE_BEGIN);
  track_event1->set_track_uuid(thread_uuid);
  track_event1->set_name("My special parent");
  packet3->set_allocated_track_event(track_event1);

  packet3->set_trusted_packet_sequence_id(trusted_packet_sequence_id);

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

  // Packets complete, write it into a file!

  {
    std::fstream output("build/direct_proto_serialization.perfetto-trace", std::ios::out | std::ios::trunc | std::ios::binary);

    std::array<Trace*, 7> traces{
      &trace1,
      &trace2,
      &trace3,
      &trace4,
      &trace5,
      &trace6,
      &trace7};

    for (const auto* trace : traces) {
      trace->SerializeToOstream(&output);
    }
  }

  google::protobuf::ShutdownProtobufLibrary();

  return 0;
}
