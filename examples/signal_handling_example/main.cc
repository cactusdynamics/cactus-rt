#include <cactus_rt/rt.h>

#include <iostream>

using cactus_rt::App;
using cactus_rt::CyclicThread;

/**
 * This is a no-op thread that does nothing at 1 kHz.
 */
class ExampleRTThread : public CyclicThread {
  int64_t loop_counter_ = 0;

 public:
  ExampleRTThread(cactus_rt::CyclicThreadConfig config) : CyclicThread(config) {}

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
  config.cpu_affinity = std::vector<size_t>{2};
  config.SetFifoScheduler(80);

  auto thread = std::make_shared<ExampleRTThread>(config);
  App  app;

  app.RegisterThread(thread);

  // Sets up the signal handlers for SIGINT and SIGTERM (by default).
  cactus_rt::SetUpTerminationSignalHandler();

  std::cout << "Testing RT loop for until CTRL+C\n";

  app.Start();

  // This function blocks until SIGINT or SIGTERM are received.
  cactus_rt::WaitForAndHandleTerminationSignal();

  app.RequestStop();
  app.Join();

  std::cout << "Number of loops executed: " << thread->GetLoopCounter() << "\n";
  return 0;
}
