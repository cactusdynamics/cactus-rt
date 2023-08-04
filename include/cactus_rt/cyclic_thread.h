#ifndef CACTUS_RT_CYCLIC_THREAD_
#define CACTUS_RT_CYCLIC_THREAD_

#include "thread.h"
#include "utils.h"

namespace cactus_rt {
class CyclicThread : public Thread {
  CyclicThreadConfig config_;
  uint64_t           period_ns_;
  struct timespec    next_wakeup_time_;

 public:
  /**
   * @brief Create a cyclic thread
   * @param name The thread name
   * @param config A cactus_rt::CyclicThreadConfig that specifies configuration parameters for this thread
   */
  CyclicThread(const char* name, CyclicThreadConfig config) : Thread(name, config),
                                                              period_ns_(config.period_ns) {
  }

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

}  // namespace cactus_rt

#endif
