#ifndef CACTUS_RT_EXAMPLES_MESSAGE_PASSING_EXAMPLE_RT_THREAD_H_
#define CACTUS_RT_EXAMPLES_MESSAGE_PASSING_EXAMPLE_RT_THREAD_H_

#include <cactus_rt/cyclic_fifo_thread.h>

#include "data_logger.h"

class RtThread : public cactus_rt::CyclicFifoThread<> {
  DataLogger& data_logger_;
  size_t      max_iterations_;
  size_t      iterations_ = 0;

 public:
  RtThread(DataLogger&         data_logger,
           int                 period_ns,
           std::vector<size_t> cpu_affinity = {},
           size_t              max_iterations = 30000)
      : CyclicFifoThread<>("RtThread",
                           period_ns,
                           80,
                           cpu_affinity),
        data_logger_(data_logger),
        max_iterations_(max_iterations) {
  }

 protected:
  bool Loop(int64_t ellapsed_ns) noexcept final;
};

#endif
