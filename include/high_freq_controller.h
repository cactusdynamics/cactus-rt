#ifndef RT_DEMO_HIGH_FREQ_CONTROLLER_H_
#define RT_DEMO_HIGH_FREQ_CONTROLLER_H_

#include <atomic>
#include <utility>

#include "data_monitor.h"
#include "framework/cyclic_rt_thread.h"

namespace rt_demo {
class HighFrequencyController : public framework::CyclicRTThread {
  using AtomicFlag = std::atomic<char>;
  static_assert(AtomicFlag::is_always_lock_free, "AtomicFlag is not lock free thus should not be used for RT on this platform");

  constexpr static char kFlagEnabledBit = 0x1;

  AtomicFlag   flag_;
  uint64_t     iterations_;
  uint64_t     max_iterations_;
  DataMonitor& data_monitor_;

 public:
  enum class WaveFunction {
    SIN,
    COS,
  };

  explicit HighFrequencyController(DataMonitor& data_monitor, uint64_t max_iteration = 15'000) : CyclicRTThread("HFC", 1'000'000),
                                                                                                 flag_(0),
                                                                                                 iterations_(0),
                                                                                                 max_iterations_(max_iteration),
                                                                                                 data_monitor_(data_monitor) {
  }

  // Do not allow rvalue reference to prevent UB.
  // TODO: not 100% certain if this is needed.
  HighFrequencyController(DataMonitor&&, int64_t) = delete;

  void SetEnabled(bool enabled) noexcept;
  void SetFunction(WaveFunction function) noexcept;

 protected:
  virtual bool Loop() noexcept override final;

 private:
  bool         IsEnabled() const noexcept;
  WaveFunction CurrentFunction() const noexcept;
};
}  // namespace rt_demo

#endif
