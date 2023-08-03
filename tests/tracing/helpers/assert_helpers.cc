#include "assert_helpers.h"

#include <google/protobuf/util/json_util.h>
#include <gtest/gtest.h>

std::string ProtoToJson(const google::protobuf::Message& proto) {
  std::string json;
  google::protobuf::util::MessageToJsonString(proto, &json);
  return json;
}

void AssertIsProcessTrackDescriptor(const TracePacket& packet, const char* process_name) {
  ASSERT_TRUE(packet.has_track_descriptor());

  const auto& track_descriptor = packet.track_descriptor();
  ASSERT_FALSE(track_descriptor.has_parent_uuid());
  ASSERT_TRUE(track_descriptor.has_uuid());
  ASSERT_TRUE(track_descriptor.uuid() > 0) << "track descriptor uuid should be > 0 but is " << track_descriptor.uuid();

  ASSERT_TRUE(track_descriptor.has_process());
  ASSERT_TRUE(track_descriptor.process().has_process_name());
  ASSERT_EQ(track_descriptor.process().process_name(), process_name);
  ASSERT_EQ(track_descriptor.process().pid(), getpid());
}

void AssertIsThreadTrackDescriptor(const TracePacket& packet, const char* thread_name, uint64_t process_track_uuid) {
  ASSERT_TRUE(packet.has_track_descriptor());

  const auto& track_descriptor = packet.track_descriptor();
  ASSERT_TRUE(track_descriptor.has_parent_uuid());
  ASSERT_EQ(track_descriptor.parent_uuid(), process_track_uuid);
  ASSERT_TRUE(track_descriptor.has_uuid());
  ASSERT_TRUE(track_descriptor.uuid() > 0) << "track descriptor uuid should be > 0 but is " << track_descriptor.uuid();

  ASSERT_TRUE(track_descriptor.has_thread());
  const auto& thread = track_descriptor.thread();
  ASSERT_TRUE(thread.has_pid());
  ASSERT_EQ(thread.pid(), getpid());
  ASSERT_TRUE(thread.has_thread_name());
  ASSERT_EQ(thread.thread_name(), thread_name);
  ASSERT_TRUE(thread.has_tid());
  ASSERT_TRUE(thread.tid() > 0) << "tid should be > 0 but is " << thread.tid();
}

void AssertIsTrackEventSliceBegin(
  const TracePacket& packet,
  const char*        event_name,
  const char*        category,
  uint64_t           thread_track_uuid,
  uint32_t           trusted_packet_sequence_id
) {
  ASSERT_TRUE(packet.has_track_event());

  const auto& track_event = packet.track_event();
  ASSERT_TRUE(track_event.has_type());
  ASSERT_EQ(track_event.type(), TrackEvent_Type_TYPE_SLICE_BEGIN);
  ASSERT_TRUE(track_event.has_name());
  ASSERT_EQ(track_event.name(), event_name);

  if (category == nullptr) {
    ASSERT_EQ(track_event.categories_size(), 0);
  } else {
    ASSERT_EQ(track_event.categories_size(), 1);
    ASSERT_EQ(track_event.categories(0), category);
  }

  ASSERT_EQ(track_event.track_uuid(), thread_track_uuid);

  ASSERT_TRUE(packet.has_trusted_packet_sequence_id());
  if (trusted_packet_sequence_id == 0) {
    ASSERT_TRUE(packet.trusted_packet_sequence_id() > 0);
  } else {
    ASSERT_EQ(packet.trusted_packet_sequence_id(), trusted_packet_sequence_id);
  }
}

void AssertIsTrackEventSliceEnd(const TracePacket& packet, uint64_t thread_track_uuid, uint32_t trusted_packet_sequence_id) {
  ASSERT_TRUE(packet.has_track_event());
  const auto& track_event = packet.track_event();

  ASSERT_EQ(track_event.type(), TrackEvent_Type_TYPE_SLICE_END);
  ASSERT_FALSE(track_event.has_name());
  ASSERT_EQ(track_event.categories_size(), 0);
  ASSERT_EQ(track_event.track_uuid(), thread_track_uuid);

  ASSERT_EQ(packet.trusted_packet_sequence_id(), trusted_packet_sequence_id);
}

void AssertIsTrackEventInstant(
  const TracePacket& packet,
  const char*        event_name,
  const char*        category,
  uint64_t           thread_track_uuid,
  uint32_t           trusted_packet_sequence_id
) {
  ASSERT_TRUE(packet.has_track_event());

  const auto& track_event = packet.track_event();
  ASSERT_TRUE(track_event.has_type());
  ASSERT_EQ(track_event.type(), TrackEvent_Type_TYPE_INSTANT);
  ASSERT_TRUE(track_event.has_name());
  ASSERT_EQ(track_event.name(), event_name);

  if (category == nullptr) {
    ASSERT_EQ(track_event.categories_size(), 0);
  } else {
    ASSERT_EQ(track_event.categories_size(), 1);
    ASSERT_EQ(track_event.categories(0), category);
  }

  ASSERT_EQ(track_event.track_uuid(), thread_track_uuid);

  ASSERT_TRUE(packet.has_trusted_packet_sequence_id());
  if (trusted_packet_sequence_id == 0) {
    ASSERT_TRUE(packet.trusted_packet_sequence_id() > 0);
  } else {
    ASSERT_EQ(packet.trusted_packet_sequence_id(), trusted_packet_sequence_id);
  }
}

void AssertTrackEventDuration(const TracePacket& packet1, const TracePacket& packet2, uint64_t min, uint64_t max) {
  ASSERT_TRUE(packet1.has_track_event());
  ASSERT_TRUE(packet2.has_track_event());
  ASSERT_EQ(packet1.track_event().type(), TrackEvent_Type_TYPE_SLICE_BEGIN);
  ASSERT_EQ(packet2.track_event().type(), TrackEvent_Type_TYPE_SLICE_END);

  ASSERT_TRUE(packet1.has_timestamp());
  ASSERT_TRUE(packet2.has_timestamp());

  ASSERT_TRUE(packet2.timestamp() > packet1.timestamp()) << "packet2 timestamp " << packet2.timestamp() << " is smaller than packet 1 timestamp " << packet1.timestamp();
  const auto delta = packet2.timestamp() - packet1.timestamp();

  ASSERT_TRUE(delta >= min) << "packet2.timestamp - packet1.timestamp ("
                            << packet2.timestamp() << " - " << packet1.timestamp() << " = " << delta << ")"
                            << " < minimum (" << min << ")";

  ASSERT_TRUE(delta <= max) << "packet2.timestamp - packet1.timestamp ("
                            << packet2.timestamp() << " - " << packet1.timestamp() << " = " << delta << ")"
                            << " > maximum (" << max << ")";
}

std::vector<const TracePacket*> GetPacketsFromTraces(const std::vector<Trace>& traces) {
  std::vector<const TracePacket*> packets;

  for (const auto& trace : traces) {
    for (int i = 0; i < trace.packet_size(); i++) {
      const TracePacket* packet = &trace.packet(i);
      packets.push_back(packet);
    }
  }
  return packets;
}

std::unordered_map<std::string, std::vector<const TracePacket*>> GetPacketsGroupByThreads(const std::vector<Trace>& traces) {
  std::unordered_map<std::string, std::vector<const TracePacket*>> packets;
  std::unordered_map<uint64_t, std::string>                        track_uuids_to_thread_names;

  // First discover all the threads!
  for (const auto& trace : traces) {
    for (int i = 0; i < trace.packet_size(); i++) {
      const TracePacket& packet = trace.packet(i);
      if (packet.has_track_descriptor() && packet.track_descriptor().has_thread()) {
        const auto& track_descriptor = packet.track_descriptor();
        if (!track_descriptor.thread().has_thread_name()) {
          throw std::runtime_error{std::string("TrackDescriptor thread should always have a name?? ") + ProtoToJson(packet)};
        }

        if (!track_descriptor.has_uuid()) {
          throw std::runtime_error{std::string("TrackDescriptor should always have an uuid?? ") + ProtoToJson(packet)};
        }

        packets[track_descriptor.thread().thread_name()].push_back(&packet);
        track_uuids_to_thread_names.emplace(track_descriptor.uuid(), track_descriptor.thread().thread_name());
      } else if (packet.has_track_event()) {
        const auto& track_event = packet.track_event();
        if (!track_event.has_track_uuid()) {
          throw std::runtime_error{"No track uuid for track event?"};
        }

        // These .at will error if the track descriptor is not seen first!
        const std::string thread_name = track_uuids_to_thread_names.at(track_event.track_uuid());
        packets.at(thread_name).push_back(&packet);
      }
    }
  }

  return packets;
}
