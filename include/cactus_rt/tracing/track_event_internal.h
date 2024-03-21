#ifndef CACTUS_RT_TRACING_TRACK_EVENT_INTERNAL_H_
#define CACTUS_RT_TRACING_TRACK_EVENT_INTERNAL_H_

#ifdef CACTUS_RT_TRACING_ENABLED
#include <cstdint>
#include <optional>
#include <variant>

#include "track_event.pb.h"

namespace cactus_rt::tracing {
/**
 * This is similar to the perfetto TrackEvent object, except it is not a
 * protobuf class and requires no dynamic allocation. It also includes some
 * data from the TracePacket.
 *
 * When emitting events for tracing, objects of this type is sent into the queue
 * instead of the protobuf object so it is real-time safe. This does mean the
 * processing thread will have to perform an additional copy from
 * TrackEventInternal to perfetto's TrackEvent, which is OK for now.
 *
 * In the longer term, this maybe replaceable with ProtoZero which is what
 * perfetto uses, which is a serialization-only protobuf library that is
 * zero copy, zero alloc, and zero syscall. Then we can use ProtoZero directly
 * in the real-time thread where the trace point is emitted and skip the copy.
 * This would only improve throughput and may actually increase latency on the
 * real time thread. More research is needed.
 *
 * Note: this event does not expose the fully capability of the perfetto
 * TrackEvent. For example, this only allows for a single category as opposed to
 * an arbitrary number of categories. This is by design as it makes the system
 * easier to deal with for real-time use cases.
 *
 * @private
 */
struct TrackEventInternal {
  using TrackEventType = cactus_tracing::vendor::perfetto::protos::TrackEvent_Type;

  uint64_t       timestamp;  // ns
  TrackEventType type;
  const char*    name = nullptr;
  const char*    category = nullptr;

  TrackEventInternal() = default;
  TrackEventInternal(
    uint64_t       _timestamp,
    TrackEventType _type,
    const char*    _name = nullptr,
    const char*    _category = nullptr
  ) : timestamp(_timestamp), type(_type), name(_name), category(_category) {}
};
}  // namespace cactus_rt::tracing
#endif
#endif
