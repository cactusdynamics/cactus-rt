#include "mock_threads.h"

#include <atomic>

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
  started_ = true;
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

cactus_rt::CyclicThreadConfig MockCyclicThread::MakeConfig(cactus_rt::ThreadTracerConfig tracer_config) {
  cactus_rt::CyclicThreadConfig config;
  config.period_ns = 1'000'000'000 / 100;  // 100 Hz
  config.tracer_config = tracer_config;
  return config;
}

MockCyclicThread::MockCyclicThread(
  const char*                   name,
  cactus_rt::ThreadTracerConfig tracer_config,
  std::function<void(int64_t)>  custom_loop_func,
  int64_t                       num_iterations
) : CyclicThread(name, MockCyclicThread::MakeConfig(tracer_config)),
    custom_loop_func_(custom_loop_func),
    num_iterations_(num_iterations) {
}

bool MockCyclicThread::Loop(int64_t /* ellapsed_ns */) noexcept {
  if (custom_loop_func_) {
    custom_loop_func_(iterations_executed_);
  } else {
    WasteTime(20us);
  }

  iterations_executed_++;
  return iterations_executed_ >= num_iterations_;
}
