#include "cyclic_rt_thread.h"

#include "rt_demo_sdt.h"

namespace rt_demo {

static int64_t TimespecDiffNanoseconds(const struct timespec& ts1, const struct timespec& ts2) {
  int64_t ts1ns = ts1.tv_sec * 1'000'000'000 + ts1.tv_nsec;
  int64_t ts2ns = ts2.tv_sec * 1'000'000'000 + ts2.tv_nsec;

  return ts1ns - ts2ns;
}

// Start -> End -> Next Wakeup Time -> Start -> End
void CyclicRTThread::Run() noexcept {
  clock_gettime(CLOCK_MONOTONIC, &next_wakeup_time_);

  struct timespec start, end;

  while (true) {
    // TODO: check for errors for all the clock_gettime?
    clock_gettime(CLOCK_MONOTONIC, &start);
    int64_t start_latency = TimespecDiffNanoseconds(start, next_wakeup_time_);
    RT_DEMO_RT_ITERATION_START(start_latency);

    if (Loop()) {
      break;
    }

    clock_gettime(CLOCK_MONOTONIC, &end);
    int64_t iteration_latency = TimespecDiffNanoseconds(end, next_wakeup_time_);
    RT_DEMO_RT_ITERATION_DONE(iteration_latency);

    // iteration_latency + start_latency is the total latency since when this
    // loop iteration is supposed to begin. If it is longer than period_ns_
    // then we have overrun and is in trouble.
    //
    // Ideally, we want to warn at a certain threshold percentage.
    if (start_latency + iteration_latency >= period_ns_) {
      // TODO: overrun signal send to somewhere.
    }

    Wait();
  }
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

}  // namespace rt_demo
