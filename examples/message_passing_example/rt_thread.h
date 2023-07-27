#ifndef CACTUS_RT_EXAMPLES_MESSAGE_PASSING_EXAMPLE_RT_THREAD_H_
#define CACTUS_RT_EXAMPLES_MESSAGE_PASSING_EXAMPLE_RT_THREAD_H_

#include <cactus_rt/rt.h>

#include <memory>

#include "data_logger_thread.h"

using cactus_rt::CyclicThread;
// "RtThread", 1'000'000, Fifo::Config{80 /* priority */}

namespace {
cactus_rt::CyclicThreadConfig MakeRealTimeThreadConfig() {
  cactus_rt::FifoThreadConfig fifo_config;
  fifo_config.priority = 80;

  cactus_rt::CyclicThreadConfig config;
  config.name = "RtThread";
  config.period_ns = 1'000'000;
  config.scheduler_config = fifo_config;

  return config;
}
}  // namespace

class RtThread : public CyclicThread {
  std::shared_ptr<DataLogger> data_logger_;
  size_t                      max_iterations_;
  size_t                      iterations_ = 0;

 public:
  RtThread(std::shared_ptr<DataLogger> data_logger, size_t max_iterations = 30000)
      : CyclicThread(MakeRealTimeThreadConfig()),
        data_logger_(data_logger),
        max_iterations_(max_iterations) {
  }

 protected:
  bool Loop(int64_t ellapsed_ns) noexcept final;
};

#endif
