#ifndef CACTUS_RT_CYCLIC_THREAD_
#define CACTUS_RT_CYCLIC_THREAD_

#include "thread.h"

namespace cactus_rt {
class CyclicThread : public Thread {
  uint64_t        period_ns_;
  struct timespec next_wakeup_time_;

 public:
  enum class LoopControl {
    Continue = 0,
    Stop,
  };

  /**
   * @brief Create a cyclic thread
   * @param name The thread name
   * @param config A cactus_rt::CyclicThreadConfig that specifies configuration parameters for this thread
   */
  CyclicThread(std::string name, CyclicThreadConfig config) : Thread(name, config),
                                                              period_ns_(config.period_ns) {
  }

 protected:
  void Run() noexcept final;

  /**
   * @brief The custom loop function that executes one iteration of the code.
   *
   * @returns LoopControl::Stop if the loop should break, LoopControl::Continue if it should not
   */
  virtual LoopControl Loop(int64_t ellapsed_ns) noexcept = 0;

  /**
   * @brief Track the latency wakeup and loop latency.
   *
   * @param wakeup_latency the latency of wakeup (scheduling latency) in us.
   * @param loop_latency the latency of Loop() call in us.
   */
  virtual void TrackLatency(int64_t /*wakeup_latency*/, int64_t /*loop_latency*/) noexcept {}
};

}  // namespace cactus_rt

#endif
