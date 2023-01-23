#ifndef CACTUS_RT_CYCLIC_THREAD_H_
#define CACTUS_RT_CYCLIC_THREAD_H_

#include <spdlog/spdlog.h>

#include <atomic>
#include <vector>

#include "cactus_rt/latency_tracker.h"
#include "cactus_rt/thread.h"
#include "cactus_rt/utils.h"

namespace cactus_rt {

// TODO: Type assertion / concept to restrict SchedulerT to viable
template <typename SchedulerT>
class CyclicThread : public Thread<SchedulerT> {
  int64_t                     period_ns_;
  struct timespec             next_wakeup_time_;
  typename SchedulerT::Config scheduler_config_;

  // Debug information
  LatencyTracker wakeup_latency_tracker_;
  LatencyTracker loop_latency_tracker_;
  LatencyTracker busy_wait_latency_tracker_;

 public:
  /**
   * Creates a thread that loops at a set period
   *
   */
  CyclicThread(const std::string&                 name,
               int64_t                            period_ns = 1'000'000,
               const typename SchedulerT::Config& config = {},
               std::vector<size_t>                cpu_affinity = {},
               size_t                             stack_size = kDefaultStackSize)
      : Thread<SchedulerT>(name, config, cpu_affinity, stack_size),
        period_ns_(period_ns),
        scheduler_config_(config) {
  }

 protected:
  void Run() noexcept final {
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
        TRACE_EVENT(kTracingCategoryInternal, "CyclicThread::Loop");
        if (Loop(loop_start - Thread<SchedulerT>::StartMonotonicTimeNs())) {
          break;
        }
      }

      loop_end = NowNs();
      loop_latency = static_cast<double>(loop_end - loop_start);

      TraceLoopEnd(loop_latency);

      TrackLatency(wakeup_latency, loop_latency);

      wakeup_latency_tracker_.RecordValue(wakeup_latency);
      loop_latency_tracker_.RecordValue(loop_latency);

      {
        TRACE_EVENT(kTracingCategoryInternal, "CyclicThread::Sleep");
        next_wakeup_time_ = AddTimespecByNs(next_wakeup_time_, period_ns_);
        busy_wait_latency = SchedulerT::Sleep(next_wakeup_time_);
      }

      busy_wait_latency_tracker_.RecordValue(busy_wait_latency);
    }
  }

  virtual bool Loop(int64_t ellapsed_ns) noexcept = 0;

  /**
   * Track the latency wakeup and loop latency. The default behavior is to track them in histograms that updates online.
   * @param wakeup_latency the latency of wakeup (scheduling latency) in us.
   * @param loop_latency the latency of Loop() call in us.
   */
  virtual void TrackLatency(double /*wakeup_latency*/, double /*loop_latency*/) noexcept {}

  void AfterRun() override {
    SPDLOG_DEBUG("wakeup_latency:");
    wakeup_latency_tracker_.DumpToLogger();

    SPDLOG_DEBUG("loop_latency:");
    loop_latency_tracker_.DumpToLogger();

    SPDLOG_DEBUG("busy_wait_latency:");
    busy_wait_latency_tracker_.DumpToLogger();
  };

 private:
  // TODO: move this method to BaseThread.
  void SetupTracingThreadTrack() const {
#ifdef ENABLE_TRACING
    // Ensures the thread track is labeled with the thread's name
    auto desc = perfetto::ThreadTrack::Current().Serialize();
    desc.mutable_thread()->set_thread_name(this->Name());
    perfetto::TrackEvent::SetTrackDescriptor(perfetto::ThreadTrack::Current(), desc);
#endif
  }

  virtual void TraceLoopStart(double /* wakeup_latency_us */) noexcept {}

  virtual void TraceLoopEnd(double /* loop_latency_us */) noexcept {}
};
}  // namespace cactus_rt

#endif
