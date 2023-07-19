#include <cactus_rt/rt.h>

#include <iostream>

using cactus_rt::App;
using cactus_rt::AppConfig;
using cactus_rt::CyclicThread;
using cactus_rt::schedulers::Deadline;

/**
 * This is a no-op thread that does nothing at 1 kHz.
 *
 * Note that we are using the Deadline scheduler as opposed to leaving the
 * template argument blank (which defaults to real-time).
 */
class ExampleDeadlineThread : public CyclicThread<Deadline> {
  int64_t loop_counter_ = 0;

 public:
  ExampleDeadlineThread() : CyclicThread<Deadline>(
                              "ExampleRTThread",
                              1'000'000,  // Period in ns
                              Deadline::Config{
                                500'000,  /* Run time in ns */
                                1'000'000 /* Deadline in ns */
                              }
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
  AppConfig config;
  config.name = "simple_deadline_example";
  App app(config);

  auto thread = std::make_shared<ExampleDeadlineThread>();

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
