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
  }

  void Start() final {
    cactus_rt::App::Start();
    auto monotonic_now = cactus_rt::NowNs();
    auto wall_now = cactus_rt::WallNowNs();
    data_logger_.Start(monotonic_now, wall_now);
    rt_thread_.Start(monotonic_now, wall_now);
  }

  void Join() {
    rt_thread_.Join();
    data_logger_.RequestStop();
    data_logger_.Join();
  }

  void Stop() {
    rt_thread_.RequestStop();
    data_logger_.RequestStop();
    Join();
  }
};

int main() {
  spdlog::set_level(spdlog::level::debug);
  RTApp app("data.csv");

  app.Start();
  app.Join();
  return 0;
}
