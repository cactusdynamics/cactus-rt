#ifndef CACTUS_RT_EXAMPLES_MUTEX_EXAMPLE_DOUBLE_BUFFER_H_
#define CACTUS_RT_EXAMPLES_MUTEX_EXAMPLE_DOUBLE_BUFFER_H_

#include <cactus_rt/mutex.h>

#include <mutex>

/**
 * A naive double buffer implementation with priority inheritance.
 *
 * Also only uses a single mutex so reads, writes, and swaps contend on a
 * single lock, which is no good for performance.
 *
 * cactus-rt already has something for this use case (real-time thread writes
 * and non-real-time thread reads) implemented via the
 * cactus_rt::experimental::lockless::spsc::RealtimeWritableValue.
 *
 * There could also be alternative implementations like:
 * https://stackoverflow.com/questions/23666069/single-producer-single-consumer-data-structure-with-double-buffer-in-c
 */
template <typename T>
class NaiveDoubleBuffer {
  T      buf_[2];  // NOLINT(modernize-avoid-c-arrays)
  size_t write_idx_ = 0;

  cactus_rt::mutex mutex_;

 public:
  void Write(const T& v) {
    const std::scoped_lock lock(mutex_);
    buf_[write_idx_] = v;
  }

  T SwapAndRead() {
    const std::scoped_lock lock(mutex_);
    write_idx_ = !write_idx_;  // NOLINT(readability-implicit-bool-conversion)
    return buf_[!write_idx_];  // NOLINT(readability-implicit-bool-conversion)
  }
};

#endif
