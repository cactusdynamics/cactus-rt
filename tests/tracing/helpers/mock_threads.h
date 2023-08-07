#ifndef CACTUS_RT_TESTS_TRACING_HELPERS_MOCK_THREADS_H_
#define CACTUS_RT_TESTS_TRACING_HELPERS_MOCK_THREADS_H_

#include <condition_variable>
#include <functional>
#include <mutex>
#include <optional>

#include "cactus_rt/cyclic_thread.h"

extern const char* kRegularThreadName;
extern const char* kCyclicThreadName;

class MockRegularThread : public cactus_rt::Thread {
  static cactus_rt::ThreadConfig MakeConfig();

  std::condition_variable                                cv_;
  std::mutex                                             mutex_;
  std::optional<std::function<void(MockRegularThread*)>> f_ = std::nullopt;

 public:
  explicit MockRegularThread(const char* name = kRegularThreadName);
  void RunOneIteration(std::function<void(MockRegularThread*)>&& f);

  // This needs to be defined as the function supplied to RunOneIteration and
  // Tracer is a protected method and therefore not accessible by f_.
  inline cactus_rt::tracing::ThreadTracer& TracerForTest() noexcept {
    return Tracer();
  }

 protected:
  void Run() final;
};

class MockCyclicThread : public cactus_rt::CyclicThread {
  static cactus_rt::CyclicThreadConfig MakeConfig();

  int64_t                   iterations_executed_ = 0;
  int64_t                   num_iterations_;
  std::chrono::microseconds time_per_iteration_;

 public:
  MockCyclicThread(
    const char*               name = kCyclicThreadName,
    int64_t                   num_iterations = 20,  // 200ms execution, which is good enough for testing.
    std::chrono::microseconds time_per_iteration = std::chrono::microseconds(1000)
  );

 protected:
  bool Loop(int64_t /* ellapsed_ns */) noexcept final;
};

#endif
