#include <spdlog/spdlog.h>
#include <unistd.h>

#include "rt/app.h"
#include "rt/cyclic_fifo_thread.h"
#include "rt/utils.h"

#define TRACEPOINT_DEFINE
#include "tracepoint_provider.h"

// A no-op thread that only serves to do nothing and measure the latency
class CyclicThread : public rt::CyclicFifoThread<> {
 public:
  CyclicThread() : rt::CyclicFifoThread<>("CyclicThread", 1'000'000, 80) {}

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

class RTApp : public rt::App {
  CyclicThread cyclic_thread_;

 public:
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

RTApp app;

int main() {
  spdlog::set_level(spdlog::level::debug);

  constexpr unsigned int time = 60;
  SPDLOG_INFO("Running for {}s", time);
  app.Start();
  sleep(time);
  app.Stop();
  return 0;
}
