#ifndef RT_DEMO_EXAMPLES_MESSAGE_PASSING_EXAMPLE_RT_THREAD_H_
#define RT_DEMO_EXAMPLES_MESSAGE_PASSING_EXAMPLE_RT_THREAD_H_

#include <rt/cyclic_fifo_thread.h>

#include "data_logger.h"

class RtThread : public rt::CyclicFifoThread {
  DataLogger& data_logger_;
  size_t      max_iterations_;
  size_t      iterations_ = 0;

 public:
  RtThread(DataLogger&         data_logger,
           int                 period_ns,
           std::vector<size_t> cpu_affinity = {},
           size_t              max_iterations = 30000,
           bool                sleep_and_busy_wait = false,
           int64_t             scheduling_latency_ns = 150'000)
      : CyclicFifoThread("RtThread",
                         period_ns,
                         80,
                         cpu_affinity,
                         sleep_and_busy_wait,
                         scheduling_latency_ns),
        data_logger_(data_logger),
        max_iterations_(max_iterations) {
  }

 protected:
  bool Loop(int64_t now) noexcept final;
};

#endif
