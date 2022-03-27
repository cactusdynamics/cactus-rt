#ifndef RT_DEMO_HIGH_FREQ_CONTROLLER_H_
#define RT_DEMO_HIGH_FREQ_CONTROLLER_H_

#include "thread.h"

namespace rt_demo {
class HighFrequencyController : public Thread {
  int state_ = 0;

 public:
  HighFrequencyController() : Thread(80, SCHED_FIFO, 0, 16 * 1024 * 1024) {}

 protected:
  virtual void Run() noexcept override;
};
}  // namespace rt_demo

#endif
