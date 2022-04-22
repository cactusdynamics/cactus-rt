#include <spdlog/spdlog.h>

#include "data_monitor.h"
#include "framework/rt_app.h"
#include "high_freq_controller.h"

class RTDemoApp : public rt_demo::framework::RTApp {
  rt_demo::DataMonitor             data_monitor_;
  rt_demo::HighFrequencyController hfc_;

 public:
  RTDemoApp(const std::string& datadir) : data_monitor_(datadir),
                                          hfc_(data_monitor_) {
    AddThread(&data_monitor_);
    AddThread(&hfc_);
  }

  virtual void Join() override {
    hfc_.Join();
    spdlog::debug("hfc joined");
    data_monitor_.RequestStop();
    data_monitor_.Join();
  }
};

RTDemoApp app{"data"};

int main(int argc, const char** argv) {
  spdlog::set_level(spdlog::level::debug);
  app.Start();
  app.Join();
  return 0;
}
