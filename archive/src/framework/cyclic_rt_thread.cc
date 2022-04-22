#include "framework/cyclic_rt_thread.h"

#include <spdlog/spdlog.h>

#include "rt_demo_sdt.h"
#include "utils/utils.h"

namespace rt_demo::framework {

// Start -> End -> Next Wakeup Time -> Start -> End
void CyclicRTThread::Run() noexcept {
  clock_gettime(CLOCK_MONOTONIC, &next_wakeup_time_);

  struct timespec start, end;

  while (true) {
    // TODO: check for errors for all the clock_gettime?
    clock_gettime(CLOCK_MONOTONIC, &start);
    int64_t wakeup_latency = utils::TimespecDiffNanoseconds(start, next_wakeup_time_);
    wakeup_latency_tracker_.AddValue(wakeup_latency);
    RT_DEMO_RT_ITERATION_START(wakeup_latency);

    if (Loop()) {
      break;
    }

    clock_gettime(CLOCK_MONOTONIC, &end);
    int64_t iteration_latency = utils::TimespecDiffNanoseconds(end, start);
    iteration_latency_tracker_.AddValue(iteration_latency);
    RT_DEMO_RT_ITERATION_DONE(iteration_latency);

    // iteration_latency + wakeup_latency is the total latency since when this
    // loop iteration is supposed to begin. If it is longer than period_ns_
    // then we have overrun and is in trouble.
    //
    // Ideally, we want to warn at a certain threshold percentage.
    if (wakeup_latency + iteration_latency >= period_ns_) {
      // TODO: overrun signal send to somewhere.
    }

    Wait();
  }
}

void CyclicRTThread::AfterRun() {
  spdlog::debug("wakeup latency:    {}\t{}\t{}", wakeup_latency_tracker_.Min() / 1000, wakeup_latency_tracker_.Mean() / 1000, wakeup_latency_tracker_.Max() / 1000);
  spdlog::debug("iteration latency: {}\t{}\t{}", iteration_latency_tracker_.Min() / 1000, iteration_latency_tracker_.Mean() / 1000, iteration_latency_tracker_.Max() / 1000);
}

void CyclicRTThread::Wait() noexcept {
  next_wakeup_time_.tv_nsec += period_ns_;
  while (next_wakeup_time_.tv_nsec >= 1'000'000'000) {
    ++next_wakeup_time_.tv_sec;
    next_wakeup_time_.tv_nsec -= 1'000'000'000;
  }

  // TODO: check for errors?
  clock_nanosleep(CLOCK_MONOTONIC, TIMER_ABSTIME, &next_wakeup_time_, NULL);
}

}  // namespace rt_demo::framework
