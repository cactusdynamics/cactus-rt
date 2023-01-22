#include "cactus_rt/cyclic_thread.h"

#include <spdlog/spdlog.h>

#include "cactus_rt/schedulers/deadline.h"
#include "cactus_rt/schedulers/fifo.h"
#include "cactus_rt/schedulers/other.h"
#include "support/tracing_perfetto_internal.h"

namespace cactus_rt {

template <typename SchedulerT>
void CyclicThread<SchedulerT>::Run() noexcept {
  SetupTracingThreadTrack();

  clock_gettime(CLOCK_MONOTONIC, &next_wakeup_time_);
  int64_t loop_start, loop_end, should_have_woken_up_at;

  int64_t wakeup_latency, loop_latency, busy_wait_latency;

  while (!this->StopRequested()) {
    should_have_woken_up_at = next_wakeup_time_.tv_sec * 1'000'000'000 + next_wakeup_time_.tv_nsec;
    loop_start = NowNs();

    wakeup_latency = loop_start - should_have_woken_up_at;

    TraceLoopStart(wakeup_latency);

    {
      TRACE_EVENT(kTracingCategory, "CyclicThread::Loop");
      if (Loop(loop_start - Thread<SchedulerT>::StartMonotonicTimeNs())) {
        break;
      }
    }

    loop_end = NowNs();
    loop_latency = static_cast<double>(loop_end - loop_start);

    TraceLoopEnd(loop_latency);

    wakeup_latency_tracker_.RecordValue(wakeup_latency);
    loop_latency_tracker_.RecordValue(loop_latency);

    {
      TRACE_EVENT(kTracingCategory, "CyclicThread::Sleep");
      next_wakeup_time_ = AddTimespecByNs(next_wakeup_time_, period_ns_);
      busy_wait_latency = SchedulerT::Sleep(next_wakeup_time_);
    }

    busy_wait_latency_tracker_.RecordValue(busy_wait_latency);
  }
}

template <typename SchedulerT>
void CyclicThread<SchedulerT>::SetupTracingThreadTrack() const {
#ifdef ENABLE_TRACING
  // Ensures the thread track is labeled with the thread's name
  auto desc = perfetto::ThreadTrack::Current().Serialize();
  desc.mutable_thread()->set_thread_name(this->Name());
  perfetto::TrackEvent::SetTrackDescriptor(perfetto::ThreadTrack::Current(), desc);
#endif
}

template <typename SchedulerT>
void CyclicThread<SchedulerT>::AfterRun() {
  SPDLOG_DEBUG("wakeup_latency:");
  wakeup_latency_tracker_.DumpToLogger();

  SPDLOG_DEBUG("loop_latency:");
  loop_latency_tracker_.DumpToLogger();

  SPDLOG_DEBUG("busy_wait_latency:");
  busy_wait_latency_tracker_.DumpToLogger();
};

// Need explicit definition because the template class of CyclicThread is not
// defined inline. This is needed because Perfetto definitions can't be
// included multiple times without a lot of problems (prior to v31).
template class CyclicThread<schedulers::Deadline>;
template class CyclicThread<schedulers::Fifo>;
template class CyclicThread<schedulers::Other>;
}  // namespace cactus_rt
