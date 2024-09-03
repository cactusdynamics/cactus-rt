#include <cactus_rt/rt.h>

#include <chrono>
#include <iostream>

#include "quill/sinks/FileSink.h"

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
    LOG_DEBUG_LIMIT(std::chrono::milliseconds{1500}, Logger(), "Log limit: Loop {}", loop_counter_);
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

  // Create a logging config to configure logging
  cactus_rt::LoggerConfig logging_config;

  // Set the background logging thread CPU affinity
  logging_config.backend_options.backend_cpu_affinity = 1;  // Different CPU than the CyclicThread CPU!

  // Configure the log level for debug messages
  logging_config.log_level = quill::LogLevel::Debug;

  logging_config.sink = cactus_rt::Frontend::create_or_get_sink<quill::FileSink>(
    "log_file",
    []() {
      quill::FileSinkConfig cfg;
      cfg.set_open_mode('w');
      cfg.set_filename_append_option(quill::FilenameAppendOption::StartDateTime);
      return cfg;
    }(),
    quill::FileEventNotifier{}
  );

  app_config.logger_config = logging_config;
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
