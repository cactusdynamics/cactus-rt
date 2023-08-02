#ifndef CACTUS_RT_TESTS_TRACING_MOCK_APP_H_
#define CACTUS_RT_TESTS_TRACING_MOCK_APP_H_

#include <chrono>
#include <condition_variable>
#include <functional>
#include <mutex>
#include <optional>

#include "cactus_rt/cyclic_thread.h"

using namespace std::chrono_literals;

class MockCyclicThread : public cactus_rt::CyclicThread {
};

class MockRegularThread : public cactus_rt::Thread {
  std::condition_variable                                cv_;
  std::mutex                                             mutex_;
  std::optional<std::function<void(MockRegularThread*)>> f_ = std::nullopt;

 public:
  MockRegularThread(cactus_rt::ThreadConfig config) : Thread(config) {}

  void RunOneIteration(std::function<void(MockRegularThread*)>&& f) {
    {
      std::scoped_lock lock(mutex_);
      if (f_.has_value()) {
        throw std::runtime_error{"f_ already set in MockRegularThread. this is a programming error"};
      }
      f_ = f;
    }

    cv_.notify_one();

    {
      std::unique_lock lock(mutex_);
      cv_.wait_for(lock, 50ms, [this]() {
        return !f_.has_value();
      });
    }
  }

  // This needs to be defined as the function supplied to RunOneIteration and
  // Tracer is a protected method and therefore not accessible by f_.
  cactus_rt::tracing::ThreadTracer& TracerForTest() noexcept {
    return Tracer();
  }

 protected:
  void Run() final {
    while (!StopRequested()) {
      {
        std::unique_lock lock(mutex_);
        cv_.wait_for(lock, 100ms, [this]() { return f_.has_value(); });
        if (!f_.has_value()) {
          continue;
        }

        f_.value()(this);
        f_ = std::nullopt;
      }

      cv_.notify_one();
    }
  }
};

#endif
