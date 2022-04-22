#ifndef RT_DEMO_RT_CYCLIC_FIFO_THREAD_H_
#define RT_DEMO_RT_CYCLIC_FIFO_THREAD_H_

#include <atomic>

#include "rt/latency_tracker.h"
#include "rt/thread.h"

namespace rt {
class CyclicFifoThread : public Thread {
  int64_t         period_ns_;
  bool            sleep_and_busy_wait_;  // Use busy wait + sleep together to achieve higher accuracy
  int64_t         scheduling_latency_ns_;
  struct timespec next_wakeup_time_;

  std::atomic_bool should_stop_ = false;

  // Debug information
  LatencyTracker wakeup_latency_tracker_;
  LatencyTracker loop_latency_tracker_;

 public:
  /**
   * Creates a thread that loops at a set period with SCHED_FIFO
   *
   * TODO: extract the options here into a struct?
   *
   * @param name The name of the thread
   * @param period_ns The period at which the Loop function is called, in nanoseconds.
   * @param sleep_and_busy_wait Use the sleep + busy wait method to potentially achieve lower jitter at the expense of CPU. Default to false.
   * @param scheduling_latency_ns The estimated scheduling delay if busy wait is to be used. No effect if not set.
   */
  CyclicFifoThread(const std::string& name,
                   int64_t            period_ns,
                   bool               sleep_and_busy_wait = false,
                   int64_t            scheduling_latency_ns = 150 * 1000,  // Assume 150 us of scheduling latency?
                   int                priority = 80,
                   uint32_t           cpu_affinity = 0,
                   size_t             stack_size = kDefaultStackSize)
      : Thread(name, priority, SCHED_FIFO, cpu_affinity, stack_size),
        period_ns_(period_ns),
        sleep_and_busy_wait_(sleep_and_busy_wait),
        scheduling_latency_ns_(scheduling_latency_ns) {
  }

  void RequestStop() noexcept {
    should_stop_.store(true);
  }

 protected:
  void Run() noexcept final;
  void AfterRun() override;

  /**
   * Called every loop.
   *
   * @returns true if exit from the loop is desired
   */
  virtual bool Loop() noexcept = 0;

  /**
   * Track the latency wakeup and loop latency. The default behavior is to track them in histograms that updates online.
   */
  virtual void TrackLatency(int64_t wakeup_latency, int64_t loop_latency) noexcept;

 private:
  void CalculateAndSetNextWakeupTime() noexcept;
  void SleepWait() noexcept;
  void SleepAndBusyWait() noexcept;

  // TODO: add lttng tracing or USDT
  inline void TraceLoopStart(int64_t /* wakeup_latency */) noexcept {}
  inline void TraceLoopEnd(int64_t /* loop_latency */) noexcept {}
};
}  // namespace rt

#endif
