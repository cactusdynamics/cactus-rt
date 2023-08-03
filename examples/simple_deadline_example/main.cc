#include <cactus_rt/rt.h>

#include <chrono>
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
  cactus_rt::CyclicThreadConfig config;

  config.name = "ExampleRTThread";
  config.period_ns = 1'000'000;
  config.SetDeadlineScheduler(500'000 /* runtime */, 1'000'000 /* deadline*/);

  auto thread = std::make_shared<ExampleDeadlineThread>(config);
  App  app;

  app.RegisterThread(thread);
  constexpr unsigned int time = 5;

  std::cout << "Testing RT loop for " << time << " seconds.\n";

  app.Start();
  std::this_thread::sleep_for(std::chrono::seconds(time));
  app.RequestStop();
  app.Join();

  std::cout << "Number of loops executed: " << thread->GetLoopCounter() << "\n";
  return 0;
}
