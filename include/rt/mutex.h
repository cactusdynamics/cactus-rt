#ifndef RT_DEMO_RT_MUTEX_H_
#define RT_DEMO_RT_MUTEX_H_

#include <pthread.h>

#include <cstring>
#include <stdexcept>

namespace rt {
/**
 * Implementation of an RT-safe mutex with pthread mutex with priority inheritance.
 *
 * Implements BasicLockable and Lockable to make it compatible with scoped_lock.
 *
 * Note, there are some confusion over whether or not unlock is a RT "safe"
 * operation as it might cause the wake-up of another thread and thus have
 * unbounded run time.
 */
class mutex {
  pthread_mutex_t m_;

 public:
  using native_handle_type = pthread_mutex_t*;

  // TODO: priority ceiling, recursive settings, process shared, robustness could be set.
  mutex() {
    pthread_mutexattr_t attr;

    int res = pthread_mutexattr_init(&attr);
    if (res != 0) {
      throw std::runtime_error{std::string("cannot pthread_mutexattr_init: ") + std::strerror(res)};
    }

    res = pthread_mutexattr_setprotocol(&attr, PTHREAD_PRIO_INHERIT);
    if (res != 0) {
      throw std::runtime_error{std::string("cannot pthread_mutexattr_setprotocol: ") + std::strerror(res)};
    }

    res = pthread_mutex_init(&m_, &attr);
    if (res != 0) {
      throw std::runtime_error{std::string("cannot pthread_mutex_init: ") + std::strerror(res)};
    }
  }

  // Do not let the mutex go out of scope without unlocking it first.
  // Destroying a locked mutex is undefined behavior.
  ~mutex() {
    // TODO: how do you handle errors? You can't throw in a destructor.
    pthread_mutex_destroy(&m_);
  }

  mutex(const mutex&) = delete;
  mutex& operator=(const mutex&) = delete;

  void lock() {
    auto res = pthread_mutex_lock(&m_);
    if (res != 0) {
      throw std::runtime_error(std::string("failed pthread_mutex_lock: ") + std::strerror(res));
    }
  }

  void unlock() noexcept {
    // The standard for BasicLockable says that unlock cannot throw, but
    // technically it can fail with a few different (unlikely) errors.
    pthread_mutex_unlock(&m_);
  }

  bool try_lock() noexcept {
    return pthread_mutex_trylock(&m_) == 0;
  }

  native_handle_type native_handle() noexcept {
    return &m_;
  };
};
}  // namespace rt

#endif
