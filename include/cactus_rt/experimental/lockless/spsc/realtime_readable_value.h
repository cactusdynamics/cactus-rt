#ifndef CACTUS_RT_EXPERIMENTAL_LOCKLESS_SPSC_REALTIME_READABLE_VALUE_
#define CACTUS_RT_EXPERIMENTAL_LOCKLESS_SPSC_REALTIME_READABLE_VALUE_

#include <atomic>
#include <memory>

namespace cactus_rt::experimental::lockless::spsc {

/**
 * This uses the CAS exchange algorithm to allow a single (real-time) thread to
 * atomically read a value of arbitrary size shared by a different
 * (non-real-time) thread.
 *
 * The original algorithm was proposed [here][1] by Dave Rowland and Fabian
 * Renn-Giles.
 *
 * The reader for this algorithm is wait-free while the writer is lock-free. The
 * reader is unable to modify the value and transmit it back to the writer with
 * this algorithm as the value will be deleted. Both read and write will incur
 * a copy.
 *
 * TODO: scope type T to be trivially copyable and default constructable?
 * TODO: at least make it so that we can initialize a struct without having to do default construction.
 * TODO: write doesn't need to be a copy if we can write directly into the new storage pointer.
 * TODO: read also potentially doesn't need a copy. However by doing that, we have to keep the writer waiting for a bit longer.
 *
 * [1]: https://www.youtube.com/watch?v=PoZAo2Vikbo
 */
template <typename T>
class RealtimeReadableValue {
  std::unique_ptr<T> storage_ptr_ = std::make_unique<T>();
  std::atomic<T*>    atomic_ptr_ = storage_ptr_.get();

 public:
  /**
   * This atomically reads the value. It returns a copy of the data.
   */
  T Read() {
    // TODO: need to figure out the atomic memory order here!
    T* data_ptr = atomic_ptr_.exchange(nullptr);
    T  data = *data_ptr;
    atomic_ptr_.store(data_ptr);
    return data;
  }

  /**
   * This atomically writes the value. It will copy the value into the storage
   * and free a previous storage pointer.
   */
  void Write(const T& new_value) {
    auto new_ptr = std::make_unique<T>(new_value);
    T*   expected;

    do {
      expected = storage_ptr_.get();
      // TODO: sequential consistency is probably too strict here. Need to
      // understand if acq_rel is sufficient.
    } while (!atomic_ptr_.compare_exchange_weak(expected, new_ptr.get()));

    // This moves new_ptr to storage_ptr, which causes storage_ptr to free up
    // whatever value was in it from before.
    storage_ptr_ = std::move(new_ptr);
  }
};

}  // namespace cactus_rt::experimental::lockless::spsc

#endif
