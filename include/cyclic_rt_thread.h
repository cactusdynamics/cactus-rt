#ifndef RT_DEMO_CYCLIC_RT_THREAD_H_
#define RT_DEMO_CYCLIC_RT_THREAD_H_

#include "thread.h"

namespace rt_demo {
class CyclicRTThread : public Thread {
  int64_t         period_ns_;
  struct timespec next_wakeup_time_;

 public:
  CyclicRTThread(int64_t  period_ns,
                 int      priority = 80,
                 uint32_t cpu_affinity = 0,
                 size_t   stack_size = 16 * 1024 * 1024)
      : Thread(priority, SCHED_FIFO, cpu_affinity, stack_size), period_ns_(period_ns) {}

 protected:
  virtual void Run() noexcept override final;
  virtual bool Loop() noexcept = 0;  // Returns true if exit is wanted.

  void Wait() noexcept;
};
}  // namespace rt_demo

#endif
