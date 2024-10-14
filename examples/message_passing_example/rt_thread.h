#ifndef CACTUS_RT_EXAMPLES_MESSAGE_PASSING_EXAMPLE_RT_THREAD_H_
#define CACTUS_RT_EXAMPLES_MESSAGE_PASSING_EXAMPLE_RT_THREAD_H_

#include <cactus_rt/rt.h>

#include <memory>

#include "data_logger_thread.h"

using cactus_rt::CyclicThread;

class RtThread : public CyclicThread {
  std::shared_ptr<DataLogger> data_logger_;
  size_t                      max_iterations_;
  size_t                      iterations_ = 0;

  static cactus_rt::CyclicThreadConfig MakeConfig() {
    cactus_rt::CyclicThreadConfig config;
    config.period_ns = 1'000'000;
    config.cpu_affinity = std::vector<size_t>{2};
    config.SetFifoScheduler(80);

    return config;
  }

 public:
  RtThread(std::shared_ptr<DataLogger> data_logger, size_t max_iterations = 30000)
      : CyclicThread("RtThread", MakeConfig()),
        data_logger_(data_logger),
        max_iterations_(max_iterations) {
  }

 protected:
  LoopControl Loop(int64_t ellapsed_ns) noexcept final;
};

#endif
