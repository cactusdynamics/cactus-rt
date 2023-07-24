#include "cactus_rt/cyclic_thread.h"

namespace cactus_rt {

namespace {
void SleepImpl(SchedulerConfigVariant config, timespec next_wakeup_time) {
  // TODO: maybe track busy wait latency? That feature is not even enabled.
  // We need to pass in the config to figure out what scheduler type we are using
  // If we are using SCHED_DEADLINE, we must sched_yield()
  if (
    std::holds_alternative<OtherThreadConfig>(config) ||
    std::holds_alternative<FifoThreadConfig>(config)
  ) {
    clock_nanosleep(CLOCK_MONOTONIC, TIMER_ABSTIME, &next_wakeup_time, nullptr);

  } else if (std::holds_alternative<DeadlineThreadConfig>(config)) {
    // Ignoring return value as man page says "In the Linux implementation, sched_yield() always succeeds."
    sched_yield();
  }
}
}  // namespace

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

    if (Loop(loop_start - Thread::StartMonotonicTimeNs())) {
      break;
    }

    TraceLoopEnd();

    loop_end = NowNs();
    loop_latency = loop_end - loop_start;
    TrackLatency(wakeup_latency, loop_latency);

    next_wakeup_time_ = AddTimespecByNs(next_wakeup_time_, static_cast<int64_t>(period_ns_));
    SleepImpl(SchedulerConfig(), next_wakeup_time_);
  }
}
}  // namespace cactus_rt
