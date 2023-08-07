#include "mock_threads.h"

#include "utils.h"

using namespace std::chrono_literals;

const char* kRegularThreadName = "MockRegularThread";
const char* kCyclicThreadName = "MockCyclicThread";

cactus_rt::ThreadConfig MockRegularThread::MakeConfig() {
  cactus_rt::ThreadConfig config;
  return config;
}

MockRegularThread::MockRegularThread(const char* name) : Thread(name, MakeConfig()) {}

void MockRegularThread::RunOneIteration(std::function<void(MockRegularThread*)>&& f) {
  {
    const std::scoped_lock lock(mutex_);
    if (f_.has_value()) {
      throw std::runtime_error{"f_ already set in MockRegularThread. this is a programming error"};
    }
    f_ = f;
  }

  cv_.notify_one();

  {
    std::unique_lock lock(mutex_);
    const auto       timed_out = cv_.wait_for(lock, 500ms, [this]() {
      return !f_.has_value();
    });

    if (!timed_out) {
      throw std::runtime_error{"timedout waiting for loop execution!"};
    }
  }
}

void MockRegularThread::Run() {
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

cactus_rt::CyclicThreadConfig MockCyclicThread::MakeConfig() {
  cactus_rt::CyclicThreadConfig config;
  config.period_ns = 1'000'000'000 / 100;  // 100 Hz
  return config;
}

MockCyclicThread::MockCyclicThread(
  const char*               name,
  int64_t                   num_iterations,
  std::chrono::microseconds time_per_iteration
) : CyclicThread(name, MockCyclicThread::MakeConfig()),
    num_iterations_(num_iterations),
    time_per_iteration_(time_per_iteration) {
}

bool MockCyclicThread::Loop(int64_t /* ellapsed_ns */) noexcept {
  WasteTime(time_per_iteration_);
  iterations_executed_++;
  return iterations_executed_ >= num_iterations_;
}
