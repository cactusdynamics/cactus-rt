#include "cactus_rt/cyclic_thread.h"

#include "cactus_rt/scheduler.h"

namespace cactus_rt {

void CyclicThread::Run() noexcept {
  // TODO: change this from CLOCK_MONOTONIC to CLOCK_MONOTONIC_RAW/CLOCK_BOOTTIME?
  clock_gettime(CLOCK_MONOTONIC, &next_wakeup_time_);
  int64_t loop_start, loop_end, should_have_woken_up_at;
  int64_t wakeup_latency, loop_latency;

  while (!this->StopRequested()) {
    should_have_woken_up_at = next_wakeup_time_.tv_nsec * 1'000'000'000 + next_wakeup_time_.tv_nsec;
    loop_start = NowNs();
    wakeup_latency = loop_start - should_have_woken_up_at;

    TraceLoopStart();

    {
      auto span = Tracer().WithSpan("CyclicThread::Loop", "cactusrt");
      if (Loop(loop_start - Thread::StartMonotonicTimeNs())) {
        break;
      }
    }

    TraceLoopEnd();

    loop_end = NowNs();
    loop_latency = loop_end - loop_start;
    TrackLatency(wakeup_latency, loop_latency);

    next_wakeup_time_ = AddTimespecByNs(next_wakeup_time_, static_cast<int64_t>(period_ns_));
    // TODO: maybe track busy wait latency? That feature is not even enabled.
    this->Config().scheduler->Sleep(next_wakeup_time_);
  }
}
}  // namespace cactus_rt
