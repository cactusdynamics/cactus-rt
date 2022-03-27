#include <spdlog/spdlog.h>

#include "high_freq_controller.h"
#include "rt_app.h"

class RTDemoApp : public rt_demo::RTApp {
 public:
  RTDemoApp() {
    AddThread(std::make_unique<rt_demo::HighFrequencyController>());
  }
};

RTDemoApp app;

int main(int argc, const char** argv) {
  spdlog::set_level(spdlog::level::debug);
  app.Start();
  app.Join();
  return 0;
}
