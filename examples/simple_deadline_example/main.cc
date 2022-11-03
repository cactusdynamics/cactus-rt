#include <cactus_rt/rt.h>
#include <spdlog/spdlog.h>
#include <unistd.h>

// A no-op thread that only serves to do nothing and measure the latency
class MyDeadlineThread : public cactus_rt::CyclicThread<cactus_rt::schedulers::Deadline> {
 public:
  MyDeadlineThread()
      : cactus_rt::CyclicThread<cactus_rt::schedulers::Deadline>("MyDeadlineThread",
                                                                 1'000'000, /* Period */
                                                                 cactus_rt::schedulers::Deadline::Config{
                                                                   500'000,  /* Run time*/
                                                                   1'000'000 /* Deadline */
                                                                 }) {}

 protected:
  bool Loop(int64_t /*now*/) noexcept final {
    return false;
  }
};

class RTApp : public cactus_rt::App {
  MyDeadlineThread cyclic_thread_;

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

  constexpr unsigned int time = 6;
  SPDLOG_INFO("Testing latency for {}s", time);
  app.Start();
  sleep(time);
  app.Stop();
  return 0;
}
