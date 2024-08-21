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

  std::atomic_bool                                       started_ = false;
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

  inline bool Started() const noexcept {
    return started_;
  }

 protected:
  void Run() final;
};

class MockCyclicThread : public cactus_rt::CyclicThread {
  static cactus_rt::CyclicThreadConfig MakeConfig(cactus_rt::ThreadTracerConfig tracer_config);

  int64_t                      iterations_executed_ = 0;
  std::function<void(int64_t)> custom_loop_func_;
  int64_t                      num_iterations_;

 public:
  MockCyclicThread(
    const char*                   name = kCyclicThreadName,
    cactus_rt::ThreadTracerConfig tracer_config = {},
    std::function<void(int64_t)>  custom_loop_func = {},
    int64_t                       num_iterations = 20  // 200ms execution, which is good enough for testing.
  );

 protected:
  LoopControl Loop(int64_t /* ellapsed_ns */) noexcept final;
};

#endif
