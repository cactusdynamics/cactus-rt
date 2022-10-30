#ifndef RT_DEMO_RT_CYCLIC_FIFO_THREAD_H_
#define RT_DEMO_RT_CYCLIC_FIFO_THREAD_H_

#include <spdlog/spdlog.h>

#include <atomic>
#include <vector>

#include "cactus_rt/latency_tracker.h"
#include "cactus_rt/thread.h"
#include "cactus_rt/utils.h"

namespace cactus_rt {
template <bool sleep_and_busy_wait = false, int64_t scheduling_latency_ns = 150'000>
class CyclicFifoThread : public Thread {
  int64_t         period_ns_;
  struct timespec next_wakeup_time_;

  std::atomic_bool should_stop_ = false;

  // Debug information
  LatencyTracker wakeup_latency_tracker_;
  LatencyTracker loop_latency_tracker_;
  LatencyTracker busy_wait_latency_tracker_;

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
  CyclicFifoThread(const std::string&  name,
                   int64_t             period_ns,
                   uint32_t            priority = 80,
                   std::vector<size_t> cpu_affinity = {},
                   size_t              stack_size = kDefaultStackSize)
      : Thread(name, priority, SCHED_FIFO, cpu_affinity, stack_size),
        period_ns_(period_ns) {
  }

  void RequestStop() noexcept {
    should_stop_.store(true);
  }

 protected:
  void Run() noexcept final {
    clock_gettime(CLOCK_MONOTONIC, &next_wakeup_time_);
    int64_t loop_start, loop_end, should_have_woken_up_at;
    double  wakeup_latency, loop_latency, busy_wait_latency;

    while (!should_stop_.load()) {
      should_have_woken_up_at = next_wakeup_time_.tv_sec * 1'000'000'000 + next_wakeup_time_.tv_nsec;
      loop_start = NowNs();

      wakeup_latency = static_cast<double>(loop_start - should_have_woken_up_at) / 1000.0;

      TraceLoopStart(wakeup_latency);

      if (Loop(loop_start - StartMonotonicTimeNs())) {
        break;
      }

      loop_end = NowNs();
      loop_latency = static_cast<double>(loop_end - loop_start) / 1000.0;

      TraceLoopEnd(loop_latency);

      TrackLatency(wakeup_latency, loop_latency);

      wakeup_latency_tracker_.RecordValue(wakeup_latency);
      loop_latency_tracker_.RecordValue(loop_latency);

      if (sleep_and_busy_wait) {
        busy_wait_latency = SleepAndBusyWait();
      } else {
        busy_wait_latency = SleepWait();
      }

      busy_wait_latency_tracker_.RecordValue(busy_wait_latency);
    }
  }

  void AfterRun() override {
    SPDLOG_DEBUG("wakeup_latency:");
    wakeup_latency_tracker_.DumpToLogger();

    SPDLOG_DEBUG("loop_latency:");
    loop_latency_tracker_.DumpToLogger();

    SPDLOG_DEBUG("busy_wait_latency:");
    busy_wait_latency_tracker_.DumpToLogger();
  }

  /**
   * Called every loop.
   *
   * @param now Ellapsed time since StartMonotonicTimeNs() in nanoseconds.
   * @returns true if exit from the loop is desired
   */
  virtual bool Loop(int64_t ellapsed_ns) noexcept = 0;

  /**
   * Track the latency wakeup and loop latency. The default behavior is to track them in histograms that updates online.
   * @param wakeup_latency the latency of wakeup (scheduling latency) in us.
   * @param loop_latency the latency of Loop() call in us.
   */
  virtual void TrackLatency(double /*wakeup_latency*/, double /*loop_latency*/) noexcept {}

 private:
  void CalculateAndSetNextWakeupTime() noexcept {
    next_wakeup_time_ = AddTimespecByNs(next_wakeup_time_, period_ns_);
  }

  /**
   * @returns the busy wait time, which is 0 here.
   */
  double SleepWait() noexcept {
    CalculateAndSetNextWakeupTime();

    // TODO: check for errors?
    // TODO: can there be remainders?
    clock_nanosleep(CLOCK_MONOTONIC, TIMER_ABSTIME, &next_wakeup_time_, NULL);
    return 0.0;
  }

  /**
   * @returns the busy wait time
   */
  double SleepAndBusyWait() noexcept {
    CalculateAndSetNextWakeupTime();

    // TODO: refactor some of these timespec -> ns int64_t conversion into an utils function
    int64_t next_wakeup_time_ns = next_wakeup_time_.tv_sec * 1'000'000'000 + next_wakeup_time_.tv_nsec;
    int64_t now = NowNs();

    // In Madden 2019 ("Challenges Using Linux as a Real-Time Operating System"),
    // the author suggested that busy wait should occur if the time to next wake
    // up is less than 2 x scheduling latency. The reason cited is because if the
    // present task goes to sleep, it may take up to 1 x scheduling latency to
    // schedule another task, and another 1 x scheduling latency to schedule the
    // present task, making it pointless.
    //
    // Perhaps my understanding is back, but I'm not sure how to measure the
    // above defined scheduling latency. I would just take the max latency number
    // from cyclictest instead, which I think is appropriate for just 1x.
    if (next_wakeup_time_ns - now >= scheduling_latency_ns) {
      struct timespec next_wakeup_time_minus_scheduling_latency = AddTimespecByNs(next_wakeup_time_, -scheduling_latency_ns);
      clock_nanosleep(CLOCK_MONOTONIC, TIMER_ABSTIME, &next_wakeup_time_minus_scheduling_latency, NULL);
    }

    now = NowNs();

    while (next_wakeup_time_ns - NowNs() > 0) {
      // busy wait
      // TODO: add asm nop? Doesn't seem necessary as we're running a bunch of clock_gettime syscalls anyway..
    }

    return static_cast<double>(NowNs() - now) / 1'000.0;
  }

  virtual void TraceLoopStart(double /* wakeup_latency_us */) noexcept {}

  virtual void TraceLoopEnd(double /* loop_latency_us */) noexcept {}
};
}  // namespace cactus_rt

#endif
