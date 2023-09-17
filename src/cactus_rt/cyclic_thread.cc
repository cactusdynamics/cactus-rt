#include "cactus_rt/cyclic_thread.h"

#include "cactus_rt/scheduler.h"

namespace cactus_rt {

void CyclicThread::Run() noexcept {
  // TODO: change this from CLOCK_MONOTONIC to CLOCK_MONOTONIC_RAW/CLOCK_BOOTTIME?
  clock_gettime(CLOCK_MONOTONIC, &next_wakeup_time_);
  int64_t next_wakeup_time_ns = next_wakeup_time_.tv_sec * 1'000'000'000 + next_wakeup_time_.tv_nsec;

  int64_t loop_start, loop_end;
  int64_t wakeup_latency, loop_latency;

  const auto tracer_config = this->Config().tracer_config;

  while (!this->StopRequested()) {
    loop_start = NowNs();
    if (tracer_config.trace_wakeup_latency) {
      Tracer().StartSpan("WakeupLatency", "cactusrt", next_wakeup_time_ns);
      Tracer().EndSpan(loop_start);
    }

    if (tracer_config.trace_loop) {
      Tracer().StartSpan("Loop", "cactusrt", loop_start);
    }

    bool should_stop = Loop(loop_start - Thread::StartMonotonicTimeNs());

    loop_end = NowNs();

    if (tracer_config.trace_loop) {
      Tracer().EndSpan(loop_end);
    }

    wakeup_latency = loop_start - next_wakeup_time_ns;
    loop_latency = loop_end - loop_start;
    TrackLatency(wakeup_latency, loop_latency);

    if (tracer_config.trace_overrun && static_cast<uint64_t>(loop_latency) >= period_ns_) {
      Tracer().InstantEvent("LoopOverrun", "cactusrt");

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
    next_wakeup_time_ns = next_wakeup_time_.tv_sec * 1'000'000'000 + next_wakeup_time_.tv_nsec;

    {
      auto span = Tracer().WithSpan("Sleep", "cactusrt", tracer_config.trace_sleep);
      // TODO: maybe track busy wait latency? That feature is not even enabled.
      this->Config().scheduler->Sleep(next_wakeup_time_);
    }
  }
}
}  // namespace cactus_rt
