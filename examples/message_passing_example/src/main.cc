#include <rt/app.h>
#include <rt/utils.h>

#include "data_logger.h"
#include "rt_thread.h"

class RTApp : public rt::App {
  DataLogger data_logger_;
  RtThread   rt_thread_;

 public:
  RTApp(const std::string& data_file_path)
      : data_logger_(data_file_path),
        rt_thread_(data_logger_, 1'000'000, 30'000, false) {
  }

  void Start() final {
    rt::App::Start();
    auto monotonic_now = rt::NowNs();
    auto wall_now = rt::WallNowNs();
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

RTApp app("data.csv");

int main() {
  app.Start();
  app.Join();
  return 0;
}
