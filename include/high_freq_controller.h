#ifndef RT_DEMO_HIGH_FREQ_CONTROLLER_H_
#define RT_DEMO_HIGH_FREQ_CONTROLLER_H_

#include <atomic>
#include <utility>

#include "cyclic_rt_thread.h"

namespace rt_demo {
class HighFrequencyController : public CyclicRTThread {
  int output_ = 0;

  // Doesn't work
  // using AtomicControlData = std::atomic<std::pair<int, float>>;
  // static_assert(AtomicControlData::is_always_lock_free, "AtomicControlData is not lock free and thus should not be used for RT");

 public:
  HighFrequencyController() : CyclicRTThread(1'000'000) {}

 protected:
  virtual bool Loop() noexcept override final;
};
}  // namespace rt_demo

#endif
