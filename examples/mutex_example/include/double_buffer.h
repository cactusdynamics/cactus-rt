#ifndef RT_DEMO_MUTEX_EXAMPLE_DOUBLE_BUFFER_H_
#define RT_DEMO_MUTEX_EXAMPLE_DOUBLE_BUFFER_H_

#include <cactus_rt/mutex.h>

#include <cstdint>
#include <mutex>

/**
 * A naive double buffer implementation with priority inheritance.
 *
 * Also only uses a single mutex so reads, writes, and swaps contend on a
 * single lock, which is no good for performance.
 *
 * Realistically, you would implement this in a lock-free manner, like this:
 * https://stackoverflow.com/questions/23666069/single-producer-single-consumer-data-structure-with-double-buffer-in-c
 */
template <typename T>
class NaiveDoubleBuffer {
  T      buf_[2];
  size_t write_idx_ = 0;

  cactus_rt::mutex mutex_;

 public:
  void Write(const T& v) {
    std::scoped_lock lock(mutex_);
    buf_[write_idx_] = v;
  }

  T SwapAndRead() {
    std::scoped_lock lock(mutex_);
    write_idx_ = !write_idx_;
    return buf_[!write_idx_];
  }
};

#endif
