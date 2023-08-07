#ifndef CACTUS_RT_TESTS_TRACING_HELPERS_ASSERT_HELPERS_H_
#define CACTUS_RT_TESTS_TRACING_HELPERS_ASSERT_HELPERS_H_

#include <cstdint>
#include <string>
#include <unordered_map>
#include <vector>

#include "trace.pb.h"
#include "trace_packet.pb.h"
#include "track_event.pb.h"

using cactus_tracing::vendor::perfetto::protos::Trace;
using cactus_tracing::vendor::perfetto::protos::TracePacket;
using cactus_tracing::vendor::perfetto::protos::TrackEvent_Type_TYPE_INSTANT;
using cactus_tracing::vendor::perfetto::protos::TrackEvent_Type_TYPE_SLICE_BEGIN;
using cactus_tracing::vendor::perfetto::protos::TrackEvent_Type_TYPE_SLICE_END;

std::string ProtoToJson(const google::protobuf::Message& proto);

void AssertIsProcessTrackDescriptor(const TracePacket& packet, const char* process_name);
void AssertIsThreadTrackDescriptor(const TracePacket& packet, const char* thread_name, uint64_t process_track_uuid);

void AssertIsTrackEventSliceBegin(
  const TracePacket& packet,
  const char*        event_name,
  const char*        category,
  uint64_t           thread_track_uuid,
  // If 0, this assertion will only check if the id is >0. Otherwise it will do an equality check
  uint32_t trusted_packet_sequence_id = 0
);

void AssertIsTrackEventSliceEnd(const TracePacket& packet, uint64_t thread_track_uuid, uint32_t trusted_packet_sequence_id);

void AssertIsTrackEventInstant(
  const TracePacket& packet,
  const char*        event_name,
  const char*        category,
  uint64_t           thread_track_uuid,
  uint32_t           trusted_packet_sequence_id = 0
);

void AssertTrackEventDuration(const TracePacket& packet1, const TracePacket& packet2, uint64_t min, uint64_t max);

std::vector<const TracePacket*> GetPacketsFromTraces(const std::vector<Trace>& traces);

std::unordered_map<std::string, std::vector<const TracePacket*>> GetPacketsGroupByThreads(const std::vector<Trace>& traces);

#endif
