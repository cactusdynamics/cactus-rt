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
                        Fifo::Config{
                          80 /* Priority */,
                        },
                        std::vector<size_t>{2} /* CPU affinity */
                      ) {}

  int64_t GetLoopCounter() const {
    return loop_counter_;
  }

 protected:
  bool Loop(int64_t /*now*/) noexcept final {
    loop_counter_++;
    if (loop_counter_ % 1000 == 0) {
      LOG_INFO(Logger(), "Loop {}", loop_counter_);
    }
    return false;
  }
};

int main() {
  auto thread = std::make_shared<ExampleRTThread>();

  // Create a Quill logging config
  quill::Config cfg;

  // Disable strict timestamp order - this will be faster, but logs may appear out of order
  cfg.backend_thread_strict_log_timestamp_order = false;

  // Set the background logging thread CPU affinity
  cfg.backend_thread_cpu_affinity = 1;  // Different CPU than the CyclicThread CPU!

  App app(cfg);

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
