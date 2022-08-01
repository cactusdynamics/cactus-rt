#include <cactus_rt/app.h>
#include <cactus_rt/cyclic_fifo_thread.h>
#include <cactus_rt/utils.h>
#include <spdlog/spdlog.h>
#include <unistd.h>

#define TRACEPOINT_DEFINE
#include "tracepoint_provider.h"

// A no-op thread that only serves to do nothing and measure the latency
class CyclicThread : public cactus_rt::CyclicFifoThread<> {
 public:
  CyclicThread() : cactus_rt::CyclicFifoThread<>("CyclicThread", 1'000'000, 80) {}

 protected:
  bool Loop(int64_t /*now*/) noexcept final {
    return false;
  }

  void TraceLoopStart(double wakeup_latency_us) noexcept override {
    tracepoint(rt_lttng_ust_example, loop_start, wakeup_latency_us);
  }

  void TraceLoopEnd(double loop_latency_us) noexcept override {
    tracepoint(rt_lttng_ust_example, loop_end, loop_latency_us);
  }
};

class RTApp : public cactus_rt::App {
  CyclicThread cyclic_thread_;

 public:
  void Start() final {
    cactus_rt::App::Start();
    auto monotonic_now = cactus_rt::NowNs();
    auto wall_now = cactus_rt::WallNowNs();
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

int main() {
  spdlog::set_level(spdlog::level::debug);

  RTApp app;

  constexpr unsigned int time = 60;
  SPDLOG_INFO("Running for {}s", time);
  app.Start();
  sleep(time);
  app.Stop();
  return 0;
}
