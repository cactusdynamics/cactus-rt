#include <cactus_rt/rt.h>

#include <iostream>

using cactus_rt::App;
using cactus_rt::CyclicThread;
using cactus_rt::schedulers::Fifo;

/**
 * This is a no-op thread that does nothing at 1 kHz.
 *
 * TODO: it should demonstrate logging and tracing capabilities.
 */
class ExampleRTThread : public CyclicThread<> {
  int64_t loop_counter_ = 0;

 public:
  ExampleRTThread() : CyclicThread<>(
                        "ExampleRTThread",
                        1'000'000,  // Period in ns
                        Fifo::Config{80 /* Priority */},
                        std::vector<size_t>{2}
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
  auto thread = std::make_shared<ExampleRTThread>();
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
