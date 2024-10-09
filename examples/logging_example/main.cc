#include <cactus_rt/rt.h>

#include <chrono>
#include <iostream>

#include "quill/LogMacros.h"  // Required for the logging macro

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

  // Create a cactus_rt app configuration
  cactus_rt::AppConfig app_config;

  // Create a Quill backend logging config to configure the Quill backend thread
  quill::BackendOptions logger_backend_options;

  // Disable strict timestamp order - this will be faster, but logs may appear out of order
  // See quill::BackendOptions documentation for more info
  logger_backend_options.log_timestamp_ordering_grace_period = std::chrono::microseconds(0);

  // Set the background logging thread CPU affinity
  logger_backend_options.cpu_affinity = 1;  // Different CPU than the CyclicThread CPU!

  app_config.logger_backend_options = logger_backend_options;
  App app("LoggingExampleApp", app_config);

  auto                   thread = app.CreateThread<ExampleRTThread>("ExampleRTThread", thread_config);
  constexpr unsigned int time = 5;

  std::cout << "Testing RT loop for " << time << " seconds.\n";

  app.Start();
  std::this_thread::sleep_for(std::chrono::seconds(time));
  app.RequestStop();
  app.Join();

  std::cout << "Number of loops executed: " << thread->GetLoopCounter() << "\n";
  return 0;
}
