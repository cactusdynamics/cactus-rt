#include <cactus_rt/rt.h>

using namespace std::literals::chrono_literals;

class RT1000 : public cactus_rt::CyclicThread {
  static cactus_rt::CyclicThreadConfig MakeConfig() {
    cactus_rt::CyclicThreadConfig config;
    config.period_ns = 1'000'000;  // 1ms period, 1000 Hz
    config.SetFifoScheduler(80);   // SCHED_FIFO, rtprio = 80
    return config;
  }

 public:
  RT1000() : CyclicThread("RT1000", MakeConfig()) {
    Logger()->set_log_level(quill::LogLevel::Debug);
  }

 protected:
  LoopControl Loop(int64_t elapsed_ns) noexcept final {
    LOG_DEBUG(Logger(), "This logs every iteration. elapsed={}ns", elapsed_ns);
    LOG_DEBUG_LIMIT(1s, Logger(), "This logs every 1s");
    return LoopControl::Continue;
  }
};

int main() {
  cactus_rt::App app;

  auto thread = app.CreateThread<RT1000>();

  app.Start();
  app.Join();

  return 0;
}
