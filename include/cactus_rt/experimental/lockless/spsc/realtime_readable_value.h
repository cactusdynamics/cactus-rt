#ifndef CACTUS_RT_EXPERIMENTAL_LOCKLESS_SPSC_REALTIME_READABLE_VALUE_
#define CACTUS_RT_EXPERIMENTAL_LOCKLESS_SPSC_REALTIME_READABLE_VALUE_

#include <atomic>
#include <memory>

namespace cactus_rt::experimental::lockless::spsc {

/**
 * This uses the CAS exchange algorithm to allow a single (real-time) thread to
 * be able to atomically read a value shared by a different (non-real-time)
 * thread.
 *
 * The reader for this algorithm is wait-free while the writer is lock-free. The
 * reader is unable to modify the value and transmit it back to the writer with
 * this algorithm.
 */
template <typename T>
class RealtimeReadableValue {
  std::unique_ptr<T> storage_ptr_ = std::make_unique<T>();
  std::atomic<T*>    atomic_ptr_ = storage_ptr_.get();

 public:
  T Read() {
    // TODO: need to figure out the atomic memory order here!
    T* data_ptr = atomic_ptr_.exchange(nullptr);
    T  data = *data_ptr;
    atomic_ptr_.store(data_ptr);
    return data;
  }

  void Write(const T& new_value) {
    auto new_ptr = std::make_unique<T>(new_value);
    T*   expected;

    do {
      expected = storage_ptr_.get();
      // TODO: sequential consistency is probably wrong here. Need to understand if acq_rel is sufficient.
    } while (!atomic_ptr_.compare_exchange_weak(expected, new_ptr.get()));

    storage_ptr_ = std::move(new_ptr);
  }
};

}  // namespace cactus_rt::experimental::lockless::spsc

#endif
