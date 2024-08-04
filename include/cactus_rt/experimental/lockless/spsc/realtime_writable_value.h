#ifndef CACTUS_RT_EXPERIMENTAL_LOCKLESS_SPSC_REALTIME_WRITABLE_VALUE_
#define CACTUS_RT_EXPERIMENTAL_LOCKLESS_SPSC_REALTIME_WRITABLE_VALUE_

#include <array>
#include <atomic>

namespace cactus_rt::experimental::lockless::spsc {

/**
 * This uses a double buffer algorithm to allow a single (real-time) thread to
 * atomically write a value of arbitrary size so it can be read by a different
 * (non-real-time) thread.
 *
 * The original algorithm was proposed [here][1] by Dave Rowland and Fabian
 * Renn-Giles.
 *
 * The writer for this algorithm is wait-free while the reader is lock-free.
 * Both read and write will incur a copy.
 *
 * TODO: write doesn't need to be copied if we write in place.
 *
 * [1]: https://www.youtube.com/watch?v=PoZAo2Vikbo
 */
template <typename T>
class RealtimeWritableValue {
  std::array<T, 2>      buf_;
  std::atomic<uint32_t> idx_ = 0;

  static constexpr uint32_t kIdxMask = 1 << 0;
  static constexpr uint32_t kNewDataMask = 1 << 1;
  static constexpr uint32_t kBusyMask = 1 << 2;

 public:
  T Read() {
    auto current = idx_.load();
    if ((current & kNewDataMask) != 0) {
      uint32_t new_value;
      do {
        current &= ~kBusyMask;  // idx only change if not busy.
        new_value = (current ^ kIdxMask) & kIdxMask;
      } while (!idx_.compare_exchange_weak(current, new_value));

      current = new_value;
    }

    return buf_[(current & kIdxMask) ^ 1];
  }

  void Write(const T& new_value) {
    // TODO: static assert that T is a POD
    auto i = idx_.fetch_or(kBusyMask) & kIdxMask;
    buf_[i] = new_value;
    idx_.store((i & kIdxMask) | kNewDataMask);
  }
};

}  // namespace cactus_rt::experimental::lockless::spsc

#endif
