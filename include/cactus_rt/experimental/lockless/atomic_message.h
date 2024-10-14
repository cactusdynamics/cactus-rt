#ifndef CACTUS_RT_EXPERIMENTAL_LOCKLESS_ATOMIC_MESSAGE_H_
#define CACTUS_RT_EXPERIMENTAL_LOCKLESS_ATOMIC_MESSAGE_H_

#include <atomic>
#include <type_traits>
#include <utility>

namespace cactus_rt::experimental::lockless {

/**
 * @brief A simple wrapper around a std::atomic to provide a real-time safe
 * compare-and-swap operation (via .Modify()).
 *
 * @tparam T the data type to be wrapped. std::atomic<T>::is_always_lock_free must be true.
 */
template <typename T, std::memory_order memory_order = std::memory_order_seq_cst>
class AtomicMessage {
  static_assert(std::atomic<T>::is_always_lock_free, "AtomicMessage<T> requires type T to be usable with std::atomic<T>::is_always_lock_free");
  std::atomic<T> data_;

 public:
  /**
   * @brief Constructs a new AtomicMessage using the constructor of the
   * underlying type.
   */
  template <typename... Args>
  AtomicMessage(Args&&... args) : data_(T(std::forward<Args>(args)...)) {}

  /**
   * @brief Returns a copy of the data in a lock-less manner.
   */
  T Read() const noexcept {
    return data_.load(memory_order);
  }

  /**
   * @brief Writes into the variable in a lock-less manner.
   */
  void Write(const T& data) noexcept {
    return data_.store(data, memory_order);
  }

  /**
   * @brief Modify the variable via an operator function in a lock-less manner (but not wait-free).
   *
   * @param f A function that takes the old value and returns the new value.
   * Maybe called multiple times. To be real-time safe, this can be a function
   * pointer or a lambda function that doesn't capture anything that can cause
   * dynamic memory allocation. This is a template instead of a std::function as
   * std::function can dynamically allocate.
   */
  template <typename Func>
  void Modify(Func f) noexcept {
    static_assert(
      std::is_nothrow_invocable_r<T, Func, T>::value,
      "Argument f to AtomicMessage::Modify requires an invocable signature T(T) noexcept"
    );

    T old_value = Read();

    while (true) {
      T new_value = f(old_value);
      if (data_.compare_exchange_weak(old_value, new_value, memory_order)) {
        break;
      }
    }
  }
};

}  // namespace cactus_rt::experimental::lockless

#endif
