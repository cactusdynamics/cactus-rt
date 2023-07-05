#include "cactus_rt/cyclic_thread.h"

namespace cactus_rt {

template <typename SchedulerT>
void CyclicThread<SchedulerT>::Run() noexcept {
  // TODO: change this from CLOCK_MONOTONIC to CLOCK_MONOTONIC_RAW/CLOCK_BOOTTIME?
  clock_gettime(CLOCK_MONOTONIC, &next_wakeup_time_);
  int64_t loop_start, loop_end, should_have_woken_up_at;
  int64_t wakeup_latency, loop_latency, busy_wait_latency;

  while (!this->StopRequested()) {
    should_have_woken_up_at = next_wakeup_time_.tv_nsec * 1'000'000'000 + next_wakeup_time_.tv_nsec;
    loop_start = NowNs();
    wakeup_latency = loop_start - should_have_woken_up_at;

    TraceLoopStart();

    if (Loop(loop_start - Thread<SchedulerT>::StartMonotonicTimeNs())) {
      break;
    }

    TraceLoopEnd();
    TrackLatency(wakeup_latency, loop_latency);

    loop_end = NowNs();
    loop_latency = loop_end - loop_start;
    next_wakeup_time_ = AddTimespecByNs(next_wakeup_time_, period_ns_);
    busy_wait_latency = SchedulerT::Sleep(next_wakeup_time_);
  }
}
}  // namespace cactus_rt
