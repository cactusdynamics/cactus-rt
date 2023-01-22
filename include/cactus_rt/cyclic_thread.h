#ifndef CACTUS_RT_CYCLIC_THREAD_H_
#define CACTUS_RT_CYCLIC_THREAD_H_

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
  void         Run() noexcept final;
  void         AfterRun() override;
  virtual bool Loop(int64_t ellapsed_ns) noexcept = 0;

 private:
  // TODO: move this method to BaseThread either by explicit instantiation of
  // Thread or move to Perfetto v32.
  void         SetupTracingThreadTrack() const;
  virtual void TraceLoopStart(double /* wakeup_latency_us */) noexcept {}
  virtual void TraceLoopEnd(double /* loop_latency_us */) noexcept {}
};
}  // namespace cactus_rt

#endif
