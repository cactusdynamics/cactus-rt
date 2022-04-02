#ifndef RT_DEMO_LOW_FREQ_CONTROLLER_H_
#define RT_DEMO_LOW_FREQ_CONTROLLER_H_

#include "data_monitor.h"
#include "framework/cyclic_rt_thread.h"
#include "high_freq_controller.h"

namespace rt_demo {
class LowFrequencyController : public framework::CyclicRTThread {
  DataMonitor&             data_monitor_;
  HighFrequencyController& hfc_;

 public:
  LowFrequencyController(DataMonitor& data_monitor, HighFrequencyController& hfc)
      : CyclicRTThread("LFC", 10'000'000'000),  // 100 Hz
        data_monitor_(data_monitor),
        hfc_(hfc) {
  }

 protected:
  virtual bool Loop() noexcept override final;
};
}  // namespace rt_demo

#endif
