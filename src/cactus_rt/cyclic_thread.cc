#include "cactus_rt/cyclic_thread.h"

#include "cactus_rt/utils.h"
#include "quill/LogMacros.h"

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
      Tracer().StartSpan("Wakeup", "cactusrt", next_wakeup_time_ns);
      Tracer().EndSpan(loop_start);
    }

    if (tracer_config.trace_loop) {
      Tracer().StartSpan("Loop", "cactusrt", loop_start);
    }

    const LoopControl loop_control = Loop(loop_start - Thread::StartMonotonicTimeNs());

    loop_end = NowNs();

    if (tracer_config.trace_loop) {
      Tracer().EndSpan(loop_end);
    }

    wakeup_latency = loop_start - next_wakeup_time_ns;
    loop_latency = loop_end - loop_start;
    TrackLatency(wakeup_latency, loop_latency);

    if (static_cast<uint64_t>(wakeup_latency + loop_latency) >= period_ns_) {
      if (tracer_config.trace_overrun) {
        Tracer().InstantEvent("LoopOverrun", "cactusrt", loop_end);

        LOG_WARNING_LIMIT(
          std::chrono::milliseconds(100),
          this->Logger(),
          "At least 1 loop overrun detected in the last 100ms: wakeup latency ({}ns) + loop latency ({}ns) > period ({}ns)",
          wakeup_latency,
          loop_latency,
          period_ns_
        );
      }
      // Loop has overrun - reset next wakeup time to now to ensure only one wakeup latency trace event is emitted
      clock_gettime(CLOCK_MONOTONIC, &next_wakeup_time_);
      next_wakeup_time_ns = next_wakeup_time_.tv_sec * 1'000'000'000 + next_wakeup_time_.tv_nsec;
    } else {
      next_wakeup_time_ = AddTimespecByNs(next_wakeup_time_, static_cast<int64_t>(period_ns_));
      next_wakeup_time_ns = next_wakeup_time_.tv_sec * 1'000'000'000 + next_wakeup_time_.tv_nsec;
    }

    if (loop_control == LoopControl::Stop) {
      break;
    }

    if (tracer_config.trace_sleep) {
      Tracer().StartSpan("Sleep", "cactusrt", loop_end);
    }

    // TODO: maybe track busy wait latency? That feature is not even enabled.
    this->Config().scheduler->Sleep(next_wakeup_time_);

    if (tracer_config.trace_sleep) {
      // Ideally this should be next iteration's loop_start, but that may cause readability and runtime performance challenges
      // Thus, the end of the sleep event may be after the end of the wakeup event by a small amount
      Tracer().EndSpan(NowNs());
    }
  }
}
}  // namespace cactus_rt
