#include "rt/cyclic_fifo_thread.h"

#include <spdlog/spdlog.h>

#include "rt/utils.h"

namespace rt {
void CyclicFifoThread::Run() noexcept {
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

    if (sleep_and_busy_wait_) {
      busy_wait_latency = SleepAndBusyWait();
    } else {
      busy_wait_latency = SleepWait();
    }

    busy_wait_latency_tracker_.RecordValue(busy_wait_latency);
  }
}

void CyclicFifoThread::AfterRun() {
  SPDLOG_DEBUG("wakeup_latency:");
  wakeup_latency_tracker_.DumpToLogger();

  SPDLOG_DEBUG("loop_latency:");
  loop_latency_tracker_.DumpToLogger();

  SPDLOG_DEBUG("busy_wait_latency:");
  busy_wait_latency_tracker_.DumpToLogger();
}

void CyclicFifoThread::CalculateAndSetNextWakeupTime() noexcept {
  next_wakeup_time_ = AddTimespecByNs(next_wakeup_time_, period_ns_);
}

double CyclicFifoThread::SleepWait() noexcept {
  CalculateAndSetNextWakeupTime();

  // TODO: check for errors?
  // TODO: can there be remainders?
  clock_nanosleep(CLOCK_MONOTONIC, TIMER_ABSTIME, &next_wakeup_time_, NULL);
  return 0.0;
}

double CyclicFifoThread::SleepAndBusyWait() noexcept {
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
  if (next_wakeup_time_ns - now >= scheduling_latency_ns_) {
    struct timespec next_wakeup_time_minus_scheduling_latency = AddTimespecByNs(next_wakeup_time_, -scheduling_latency_ns_);
    clock_nanosleep(CLOCK_MONOTONIC, TIMER_ABSTIME, &next_wakeup_time_minus_scheduling_latency, NULL);
  }

  now = NowNs();

  while (next_wakeup_time_ns - NowNs() > 0) {
    // busy wait
    // TODO: add asm nop? Doesn't seem necessary as we're running a bunch of clock_gettime syscalls anyway..
  }

  return static_cast<double>(NowNs() - now) / 1'000.0;
}

}  // namespace rt
