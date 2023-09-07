#include "cactus_rt/cyclic_thread.h"

#include "cactus_rt/scheduler.h"

namespace cactus_rt {

void CyclicThread::Run() noexcept {
  // TODO: change this from CLOCK_MONOTONIC to CLOCK_MONOTONIC_RAW/CLOCK_BOOTTIME?
  clock_gettime(CLOCK_MONOTONIC, &next_wakeup_time_);
  int64_t loop_start, loop_end, should_have_woken_up_at;
  int64_t wakeup_latency, loop_latency;

  const auto tracer_config = this->Config().tracer_config;

  while (!this->StopRequested()) {
    should_have_woken_up_at = next_wakeup_time_.tv_nsec * 1'000'000'000 + next_wakeup_time_.tv_nsec;
    loop_start = NowNs();
    wakeup_latency = loop_start - should_have_woken_up_at;

    bool should_stop;
    if (tracer_config.trace_loop) {
      Tracer().StartSpan("CyclicThread::Loop", "cactusrt", loop_start);
    }

    should_stop = Loop(loop_start - Thread::StartMonotonicTimeNs());

    loop_end = NowNs();

    if (tracer_config.trace_loop) {
      Tracer().EndSpan(loop_end);
    }

    loop_latency = loop_end - loop_start;
    TrackLatency(wakeup_latency, loop_latency);

    if (tracer_config.trace_overrun && static_cast<uint64_t>(loop_latency) >= period_ns_) {
      Tracer().InstantEvent("CyclicThread::LoopOverrun", "cactusrt");

      LOG_WARNING_LIMIT(
        std::chrono::milliseconds(100),
        this->Logger(),
        "At least 1 loop overrun detected in the last 100ms: latency ({}ns) > period ({}ns)",
        loop_latency,
        period_ns_
      );
    }

    if (should_stop) {
      break;
    }

    next_wakeup_time_ = AddTimespecByNs(next_wakeup_time_, static_cast<int64_t>(period_ns_));

    {
      auto span = Tracer().WithSpan("CyclicThread::Sleep", "cactusrt", tracer_config.trace_sleep);
      // TODO: maybe track busy wait latency? That feature is not even enabled.
      this->Config().scheduler->Sleep(next_wakeup_time_);
    }
  }
}
}  // namespace cactus_rt
