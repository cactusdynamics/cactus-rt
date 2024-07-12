#ifndef CACTUS_RT_EXPERIMENTAL_LOCKLESS_ATOMIC_BITSET_H_
#define CACTUS_RT_EXPERIMENTAL_LOCKLESS_ATOMIC_BITSET_H_

#include <atomic>
#include <cstddef>
#include <initializer_list>
#include <limits>

namespace cactus_rt::experimental::lockless {

template <typename T>
class AtomicBitset {
  static_assert(std::atomic<T>::is_always_lock_free);
  std::atomic<T> data_;

  // Avoid any casting that might occur during bit shifting later.
  static constexpr T kOne = 1;

 public:
  static constexpr size_t kCapacity = std::numeric_limits<T>::digits;

  /**
   * Always initialize the bitset to be 0 at the start.
   */
  AtomicBitset() : data_(0) {}

  void Set(const size_t i, const std::memory_order order = std::memory_order_seq_cst);

  void SetRange(const std::initializer_list<size_t> indices, const std::memory_order order = std::memory_order_seq_cst);

  void Reset(const size_t i, const std::memory_order order = std::memory_order_seq_cst);

  void ResetRange(const std::initializer_list<size_t> indices, const std::memory_order order = std::memory_order_seq_cst);

  void Flip(const size_t t, const std::memory_order order = std::memory_order_seq_cst);

  void FlipRange(const std::initializer_list<size_t> indices, const std::memory_order order = std::memory_order_seq_cst);

  void SetValue(const size_t i, const bool value, const std::memory_order order = std::memory_order_seq_cst);

  bool Test(const size_t i, const std::memory_order order = std::memory_order_seq_cst) const;

  T Value(const std::memory_order order = std::memory_order_seq_cst) const {
    return data_.load(order);
  }

  bool operator[](const size_t i) const {
    return Test(i);
  }
};

}  // namespace cactus_rt::experimental::lockless

#endif
