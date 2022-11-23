#include <cactus_rt/rt.h>
#include <spdlog/spdlog.h>
#include <unistd.h>

// A no-op thread that only serves to do nothing and measure the latency
class CyclicThread : public cactus_rt::CyclicThread<cactus_rt::schedulers::Fifo> {
 public:
  CyclicThread(std::vector<size_t> cpu_affinity)
      : cactus_rt::CyclicThread<cactus_rt::schedulers::Fifo>("CyclicThread", 1'000'000, /* Period */
                                                             cactus_rt::schedulers::Fifo::Config{80 /* Priority */},
                                                             cpu_affinity) {}

 protected:
  bool Loop(int64_t /*now*/) noexcept final {
    return false;
  }
};

class RTApp : public cactus_rt::App {
  CyclicThread thread_;

 public:
  RTApp(std::vector<size_t> cpu_affinity) : thread_(cpu_affinity) {
    RegisterThread(thread_);
  }

  void Stop() {
    thread_.RequestStop();
    thread_.Join();
  }
};

int main() {
  spdlog::set_level(spdlog::level::debug);

  RTApp app(std::vector<size_t>{2});

  constexpr unsigned int time = 5;
  SPDLOG_INFO("Testing latency for {}s", time);
  app.Start();
  sleep(time);
  app.Stop();
  return 0;
}
