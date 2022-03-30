#include <spdlog/spdlog.h>

#include "data_monitor.h"
#include "framework/rt_app.h"
#include "high_freq_controller.h"

class RTDemoApp : public rt_demo::framework::RTApp {
 public:
  RTDemoApp() {
    auto data_monitor = std::make_unique<rt_demo::DataMonitor>();
    // TODO: Is this dangerous given that we move it later... :D..
    // Maybe it works, but the design might be bad.
    AddThread(std::make_unique<rt_demo::HighFrequencyController>(*data_monitor));
    AddThread(std::move(data_monitor));
  }
};

RTDemoApp app;

int main(int argc, const char** argv) {
  spdlog::set_level(spdlog::level::debug);
  app.Start();
  app.Join();
  return 0;
}
