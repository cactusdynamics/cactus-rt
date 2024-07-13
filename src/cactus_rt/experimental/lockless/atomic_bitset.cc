#include "cactus_rt/experimental/lockless/atomic_bitset.h"

#include <cassert>  // TODO: switch to some sort of bounded integer arrangement.

namespace cactus_rt::experimental::lockless {
template <typename T>
void AtomicBitset<T>::Set(const size_t i, const std::memory_order order) {
  assert(i < kCapacity);

  T bitmask = kOne << static_cast<T>(i);
  data_.fetch_or(bitmask, order);
}

template <typename T>
void AtomicBitset<T>::SetRange(const std::initializer_list<size_t> indices, const std::memory_order order) {
  T bitmask = 0;
  for (const auto i : indices) {
    assert(i < kCapacity);
    bitmask |= (kOne << static_cast<T>(i));
  }

  data_.fetch_or(bitmask, order);
}

template <typename T>
void AtomicBitset<T>::Reset(const size_t i, const std::memory_order order) {
  assert(i < kCapacity);

  T bitmask = ~(kOne << static_cast<T>(i));
  data_.fetch_and(bitmask, order);
}

template <typename T>
void AtomicBitset<T>::ResetRange(const std::initializer_list<size_t> indices, const std::memory_order order) {
  T bitmask = 0;
  for (const auto i : indices) {
    assert(i < kCapacity);
    bitmask |= (kOne << static_cast<T>(i));
  }

  bitmask = ~(bitmask);
  data_.fetch_and(bitmask, order);
}

template <typename T>
void AtomicBitset<T>::Flip(const size_t i, const std::memory_order order) {
  assert(i < kCapacity);

  T bitmask = kOne << static_cast<T>(i);
  data_.fetch_xor(bitmask, order);
}

template <typename T>
void AtomicBitset<T>::FlipRange(const std::initializer_list<size_t> indices, const std::memory_order order) {
  T bitmask = 0;
  for (const auto i : indices) {
    assert(i < kCapacity);
    bitmask |= (kOne << static_cast<T>(i));
  }

  data_.fetch_xor(bitmask, order);
}

template <typename T>
void AtomicBitset<T>::SetValue(const size_t i, const bool value, const std::memory_order order) {
  assert(i < kCapacity);

  if (value) {
    Set(i, order);
  } else {
    Reset(i, order);
  }
}

template <typename T>
bool AtomicBitset<T>::Test(const size_t i, const std::memory_order order) const {
  assert(i < kCapacity);

  T bitmask = kOne << static_cast<T>(i);
  return data_.load(order) & bitmask;
}

#if (ATOMIC_LLONG_LOCK_FREE == 2)
template class AtomicBitset<unsigned long long>;
#endif

#if (ATOMIC_LONG_LOCK_FREE == 2)
template class AtomicBitset<unsigned long>;
#endif

#if (ATOMIC_INT_LOCK_FREE == 2)
template class AtomicBitset<unsigned int>;
#endif

}  // namespace cactus_rt::experimental::lockless
