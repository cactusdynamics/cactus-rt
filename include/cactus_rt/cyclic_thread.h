#ifndef CACTUS_RT_CYCLIC_THREAD_
#define CACTUS_RT_CYCLIC_THREAD_

#include "schedulers/deadline.h"
#include "schedulers/fifo.h"
#include "schedulers/other.h"
#include "thread.h"
#include "utils.h"

namespace cactus_rt {
template <typename SchedulerT = schedulers::Fifo>
class CyclicThread : public Thread<SchedulerT> {
  int64_t         period_ns_;
  struct timespec next_wakeup_time_;

 public:
  CyclicThread(
    std::string                 name,
    int64_t                     period_ns = 1'000'000,
    typename SchedulerT::Config config = {},
    std::vector<size_t>         cpu_affinity = {},
    size_t                      stack_size = kDefaultStackSize
  ) : Thread<SchedulerT>(name, config, cpu_affinity, stack_size),
      period_ns_(period_ns) {}

 protected:
  void Run() noexcept final;

  /**
   * @brief The custom loop function that executes one iteration of the code.
   *
   * @returns true if the loop should break, false if it should not
   */
  virtual bool Loop(int64_t ellapsed_ns) noexcept = 0;

  /**
   * @brief Track the latency wakeup and loop latency.
   *
   * @param wakeup_latency the latency of wakeup (scheduling latency) in us.
   * @param loop_latency the latency of Loop() call in us.
   */
  virtual void TrackLatency(int64_t /*wakeup_latency*/, int64_t /*loop_latency*/) noexcept {}

  /**
   * @brief This function is called before each loop iteration. It is intended to act as a trace point.
   */
  virtual void TraceLoopStart() noexcept {}

  /**
   * @brief This function is called after each loop iteration. It is intended to act as a trace point.
   */
  virtual void TraceLoopEnd() noexcept {}
};

// Deadline needs access to the cyclic thread's period
// This template specialization avoids needing to pass the thread into a Deadline::SetThreadScheduling by
// manually overriding the period of Deadline::Config in the template-specialized constructor. User setting of sched_period directly on the Deadline::Config object for cyclic threads is
// not supported.
template <>
inline CyclicThread<schedulers::Deadline>::CyclicThread(
  std::string                  name,
  int64_t                      period_ns,
  schedulers::Deadline::Config config,
  std::vector<size_t>          cpu_affinity,
  size_t                       stack_size
) : Thread<schedulers::Deadline>(name, config, cpu_affinity, stack_size),
    period_ns_(period_ns) {
  SchedulerConfig().sched_period_ns = static_cast<uint64_t>(period_ns);
}

template class CyclicThread<schedulers::Other>;
template class CyclicThread<schedulers::Fifo>;
template class CyclicThread<schedulers::Deadline>;
}  // namespace cactus_rt

#endif
