#include <cactus_rt/rt.h>

#include <chrono>
#include <iostream>

#include "quill/backend/BackendOptions.h"
#include "quill/sinks/ConsoleSink.h"
#include "quill/sinks/FileSink.h"

// Required to parse std::chrono inside logging macros
#include "quill/std/Chrono.h"  // IWYU pragma: keep

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
  LoopControl Loop(int64_t elapsed_ns) noexcept final {
    loop_counter_++;
    if (loop_counter_ % 1000 == 0) {
      LOG_INFO(Logger(), "Loop {} ({})", loop_counter_, std::chrono::nanoseconds(elapsed_ns));
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
  quill::BackendOptions logger_backend_options = cactus_rt::logging::DefaultBackendOptions();

  // Disable strict timestamp order by setting the grace period to 0 - this will be faster, but logs may appear out of order
  // See quill::BackendOptions documentation for more info
  // TODO: There is a bug in quill where setting the grace period to 0 causes assertion error in Debug builds. This is fixed in 7.4.0 (https://github.com/odygrd/quill/issues/605)
  logger_backend_options.log_timestamp_ordering_grace_period = std::chrono::microseconds(1);

  // Set the background logging thread CPU affinity
  logger_backend_options.cpu_affinity = 1;  // Different CPU than the CyclicThread CPU!

  app_config.logger_backend_options = logger_backend_options;
  App app("LoggingExampleApp", app_config);

  auto thread = app.CreateThread<ExampleRTThread>("ExampleRTThread", thread_config);

  // Create another thread with a custom logger, which has multiple sinks
  cactus_rt::CyclicThreadConfig other_thread_config = thread_config;  // Copy thread config

  // Create another console sink
  // Make sure to use cactus_rt's logging Frontend instead of Quill's default
  auto console_sink = cactus_rt::logging::Frontend::create_or_get_sink<quill::ConsoleSink>("OtherConsoleSink", true);

  // Create a file sink too
  quill::FileSinkConfig file_sink_config;
  file_sink_config.set_open_mode('w');
  file_sink_config.set_filename_append_option(quill::FilenameAppendOption::StartDateTime);
  auto file_sink = cactus_rt::logging::Frontend::create_or_get_sink<quill::FileSink>(
    "file_logging_example.log",
    file_sink_config,
    quill::FileEventNotifier{}
  );

  // Add both sinks to a vector
  const std::vector<std::shared_ptr<quill::Sink>> sinks = {console_sink, file_sink};

  // Create a custom formatter pattern
  auto pattern_format = quill::PatternFormatterOptions(
    "[%(time)][%(log_level_short_code)][%(logger)][%(process_id)][%(file_name):%(line_number)] - WOW custom message format - %(message)",
    "%H:%M:%S.%Qns"
  );

  // Use the new sinks and pattern to create a custom logger for the other thread
  auto* custom_thread_logger = cactus_rt::logging::Frontend::create_or_get_logger("CustomThreadLogger", sinks, pattern_format);
  other_thread_config.logger_config.logger_name = custom_thread_logger->get_logger_name();

  // Add a second instance of the example thread class, which uses the configuration with the new logger
  auto other_thread = app.CreateThread<ExampleRTThread>("OtherExampleRTThread", other_thread_config);

  // Start the app
  constexpr unsigned int time = 5;

  std::cout << "Testing RT loop for " << time << " seconds.\n";

  app.Start();
  std::this_thread::sleep_for(std::chrono::seconds(time));
  app.RequestStop();
  app.Join();

  std::cout << "Number of loops executed: " << thread->GetLoopCounter() << "\n";
  return 0;
}
