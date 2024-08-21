#include <cactus_rt/rt.h>

#include <chrono>
#include <iostream>

using cactus_rt::App;
using cactus_rt::CyclicThread;

/**
 * This is a no-op thread that does nothing at 1 kHz.
 *
 */
class ExampleRTThread : public CyclicThread {
  int64_t loop_counter_ = 0;

 public:
  ExampleRTThread(const char* name, cactus_rt::CyclicThreadConfig config) : CyclicThread(name, config) {}

  int64_t GetLoopCounter() const {
    return loop_counter_;
  }

 protected:
  LoopControl Loop(int64_t /*now*/) noexcept final {
    loop_counter_++;
    if (loop_counter_ % 1000 == 0) {
      LOG_INFO(Logger(), "Loop {}", loop_counter_);
    }
    LOG_INFO_LIMIT(std::chrono::milliseconds{1500}, Logger(), "Log limit: Loop {}", loop_counter_);
    return LoopControl::Continue;
  }
};

int main() {
  cactus_rt::CyclicThreadConfig thread_config;
  thread_config.period_ns = 1'000'000;
  thread_config.cpu_affinity = std::vector<size_t>{2};
  thread_config.SetFifoScheduler(80);

  auto thread = std::make_shared<ExampleRTThread>("ExampleRTThread", thread_config);

  // Create a cactus_rt app configuration
  cactus_rt::AppConfig app_config;

  // Create a Quill logging config to configure logging
  quill::Config logging_config;

  // Disable strict timestamp order - this will be faster, but logs may appear out of order
  logging_config.backend_thread_strict_log_timestamp_order = false;

  // Set the background logging thread CPU affinity
  logging_config.backend_thread_cpu_affinity = 1;  // Different CPU than the CyclicThread CPU!

  app_config.logger_config = logging_config;
  App app("LoggingExampleApp", app_config);

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
