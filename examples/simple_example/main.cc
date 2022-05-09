#include <spdlog/spdlog.h>
#include <unistd.h>

#include "rt/app.h"
#include "rt/cyclic_fifo_thread.h"
#include "rt/utils.h"

// A no-op thread that only serves to do nothing and measure the latency
class CyclicThread : public rt::CyclicFifoThread<> {
 public:
  CyclicThread(std::vector<size_t> cpu_affinity) : rt::CyclicFifoThread<>("CyclicThread", 1'000'000, 80, cpu_affinity, false) {}

 protected:
  bool Loop(int64_t /*now*/) noexcept final {
    return false;
  }
};

class RTApp : public rt::App {
  CyclicThread cyclic_thread_;

 public:
  RTApp(std::vector<size_t> cpu_affinity) : cyclic_thread_(cpu_affinity) {}

  void Start() final {
    rt::App::Start();
    auto monotonic_now = rt::NowNs();
    auto wall_now = rt::WallNowNs();
    cyclic_thread_.Start(monotonic_now, wall_now);
  }

  void Join() {
    cyclic_thread_.Join();
  }

  void Stop() {
    cyclic_thread_.RequestStop();
    Join();
  }
};

static const std::vector<size_t> cpu_affinity = {2};

RTApp app(cpu_affinity);

int main() {
  spdlog::set_level(spdlog::level::debug);

  constexpr unsigned int time = 60;
  SPDLOG_INFO("Testing latency for {}s", time);
  app.Start();
  sleep(time);
  app.Stop();
  return 0;
}
