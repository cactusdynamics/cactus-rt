#include <pthread.h>

#include <array>
#include <cstring>
#include <iostream>
#include <mutex>
#include <stdexcept>
#include <thread>

// DO NOT USE THIS CODE. DEMONSTRATION ONLY.
// See https://shuhaowu.com/blog/2022/04-linux-rt-appdev-part4.html
// Instead, use the rt::thread in libs/rt.

namespace rt {
class mutex {
  pthread_mutex_t m_;

 public:
  using native_handle_type = pthread_mutex_t*;

  mutex() {
    pthread_mutexattr_t attr;

    int res = pthread_mutexattr_init(&attr);
    if (res != 0) {
      throw std::runtime_error{std::strerror(res)};
    }

    res = pthread_mutexattr_setprotocol(&attr, PTHREAD_PRIO_INHERIT);
    if (res != 0) {
      throw std::runtime_error{std::strerror(res)};
    }

    res = pthread_mutex_init(&m_, &attr);
    if (res != 0) {
      throw std::runtime_error{std::strerror(res)};
    }
  }

  ~mutex() {
    pthread_mutex_destroy(&m_);
  }

  mutex(const mutex&) = delete;
  mutex& operator=(const mutex&) = delete;

  void lock() {
    auto res = pthread_mutex_lock(&m_);
    if (res != 0) {
      throw std::runtime_error(std::strerror(res));
    }
  }

  void unlock() noexcept {
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

rt::mutex          mut;
std::array<int, 3> a;

void Write(int v) {
  std::scoped_lock lock(mut);
  a[0] = v;
  a[1] = 2 * v;
  a[2] = 3 * v;
}

int Read() {
  std::scoped_lock lock(mut);
  return a[0] + a[1] + a[2];
}

int main() {
  // Non RT thread is fine. This is just an example to use the above mutex class.
  // Note: not guaranteed to print 30 in the console, as t2 can happen before t1.
  std::thread t1([]() {
    Write(5);
  });

  std::thread t2([]() {
    std::cout << Read() << "\n";
  });

  t1.join();
  t2.join();

  return 0;
}
