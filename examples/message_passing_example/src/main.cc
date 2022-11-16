#include <cactus_rt/app.h>
#include <cactus_rt/utils.h>

#include "data_logger.h"
#include "rt_thread.h"

class RTApp : public cactus_rt::App {
  DataLogger data_logger_;
  RtThread   rt_thread_;

 public:
  RTApp(const std::string& data_file_path) noexcept
      : data_logger_(data_file_path),
        rt_thread_(data_logger_, 1'000'000, std::vector<size_t>(), 30'000) {
    RegisterThread(data_logger_);
    RegisterThread(rt_thread_);
  }

  void Join() override {
    rt_thread_.Join();
    data_logger_.RequestStop();
    data_logger_.Join();
  }
};

int main() {
  spdlog::set_level(spdlog::level::debug);
  RTApp app("data.csv");

  app.Start();
  app.Join();
  return 0;
}
