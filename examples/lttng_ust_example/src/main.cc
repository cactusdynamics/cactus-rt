#include <cactus_rt/rt.h>
#include <spdlog/spdlog.h>
#include <unistd.h>

#define TRACEPOINT_DEFINE
#include "tracepoint_provider.h"

// A no-op thread that only serves to do nothing and measure the latency
class CyclicThread : public cactus_rt::CyclicThread<cactus_rt::schedulers::Fifo> {
 public:
  CyclicThread()
      : cactus_rt::CyclicThread<cactus_rt::schedulers::Fifo>("CyclicThread", 1'000'000,
                                                             cactus_rt::schedulers::Fifo::Config{80 /* priority */}) {}

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
  RTApp() {
    RegisterThread(cyclic_thread_);
  }

  void Stop() {
    cyclic_thread_.RequestStop();
    Join();
  }
};

int main() {
  spdlog::set_level(spdlog::level::debug);

  RTApp app;

  constexpr unsigned int time = 30;
  SPDLOG_INFO("Running for {}s", time);
  app.Start();
  sleep(time);
  app.Stop();
  return 0;
}
