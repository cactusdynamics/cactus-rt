#ifndef CACTUS_TRACING_TRACK_EVENT_H_
#define CACTUS_TRACING_TRACK_EVENT_H_

#include <cstdint>
#include <optional>
#include <type_traits>
#include <variant>

namespace cactus_tracing {
/**
 * This is similar to the perfetto TrackEvent. We use a struct so we don't have
 * to dynamically allocate on the real-time thread. This means there will be an
 * additional copy on the non-real-time thread, which is fine for now.
 *
 * In the longer term, this maybe replaceable with ProtoZero which is what
 * perfetto uses, but need to make sure that library doesn't have problems with
 * real-time. See: https://perfetto.dev/docs/design-docs/protozero
 *
 * Note, this only allows for a single category even tho perfetto allows
 * arbitrary number. This makes it easier to deal with.
 */
struct TrackEvent {
  enum class Type {
    UNSPECIFIED = 0,
    SLICE_BEGIN = 1,
    SLICE_END = 2,
    INSTANT = 3,
    COUNTER = 4,
  };

  uint64_t    timestamp;
  Type        type = Type::UNSPECIFIED;
  const char* name = nullptr;
  const char* category = nullptr;

  // std::variant is real time safe but boost::variant is not. See
  // https://youtu.be/Tof5pRedskI?t=1851
  // boost::variant: if the constructor of the object fails, it will rollback
  // the value to before, which means there is a backup must be taken with
  // memory allocation (strong-exception guarantee).
  // std::variant does not have strong-exception guarantee so no allocation.
  std::optional<std::variant<int64_t, double>> counter_value = std::nullopt;

  TrackEvent() = default;
  TrackEvent(uint64_t _timestamp, Type _type, const char* _name = nullptr, const char* _category = nullptr)
      : timestamp(_timestamp), type(_type), name(_name), category(_category) {}
};

template <typename E>
constexpr auto to_underlying(E e) noexcept {
  return static_cast<std::underlying_type_t<E>>(e);
}

}  // namespace cactus_tracing

#endif
