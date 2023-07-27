#include <cactus_rt/rt.h>

#include <iostream>

using cactus_rt::App;
using cactus_rt::CyclicThread;

/**
 * This is a no-op thread that does nothing at 1 kHz.
 *
 * Note that we are using the Deadline scheduler as opposed to leaving the
 * template argument blank (which defaults to real-time).
 */
class ExampleDeadlineThread : public CyclicThread {
  int64_t loop_counter_ = 0;

 public:
  ExampleDeadlineThread(cactus_rt::CyclicThreadConfig config) : CyclicThread(config
                                                                ) {}

  int64_t GetLoopCounter() const {
    return loop_counter_;
  }

 protected:
  bool Loop(int64_t /*now*/) noexcept final {
    loop_counter_++;
    return false;
  }
};

int main() {
  cactus_rt::DeadlineThreadConfig deadline_config;
  deadline_config.sched_deadline_ns = 1'000'000;
  deadline_config.sched_runtime_ns = 500'000;
  deadline_config.sched_period_ns = 1'000'000;

  cactus_rt::CyclicThreadConfig config;
  config.name = "ExampleRTThread";

  // config.cpu_affinity = std::vector<size_t>{2};

  config.scheduler_config = deadline_config;
  auto thread = std::make_shared<ExampleDeadlineThread>(config);
  App  app;

  app.RegisterThread(thread);
  constexpr unsigned int time = 5;

  std::cout << "Testing RT loop for " << time << " seconds.\n";

  app.Start();
  sleep(time);
  app.RequestStop();
  app.Join();

  std::cout << "Number of loops executed: " << thread->GetLoopCounter() << "\n";
  return 0;
}
