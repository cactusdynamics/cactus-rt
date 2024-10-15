#include "cactus_rt/logging.h"

#include <chrono>
#include <memory>
#include <string>

#include "quill/Logger.h"
#include "quill/backend/BackendOptions.h"
#include "quill/core/PatternFormatterOptions.h"
#include "quill/sinks/ConsoleSink.h"
#include "quill/sinks/Sink.h"

quill::BackendOptions cactus_rt::logging::DefaultBackendOptions() {
  // Many of the default options set by Quill are already OK for real-time logging
  quill::BackendOptions default_backend_options;

  // Disable strict timestamp order by setting the grace period to 0 - this will be faster, but logs may appear out of order
  // See quill::BackendOptions documentation for more info
  // TODO: There is a bug in quill where setting the grace period to 0 causes assertion error in Debug builds. This is fixed in 7.4.0 (https://github.com/odygrd/quill/issues/605)
  default_backend_options.log_timestamp_ordering_grace_period = std::chrono::milliseconds(1);

  return default_backend_options;
}

cactus_rt::logging::Logger* cactus_rt::logging::DefaultLogger(std::string logger_name) {
  return cactus_rt::logging::Frontend::create_or_get_logger(
    logger_name,
    DefaultConsoleSink(),
    DefaultPatternFormatterOptions()
  );
}

std::string cactus_rt::logging::DefaultConsoleSinkName() { return "DefaultConsoleSink"; }

std::shared_ptr<quill::Sink> cactus_rt::logging::DefaultConsoleSink() {
  return cactus_rt::logging::Frontend::create_or_get_sink<quill::ConsoleSink>(
    cactus_rt::logging::DefaultConsoleSinkName(),
    true  // Enable console colours
  );
}

quill::PatternFormatterOptions cactus_rt::logging::DefaultPatternFormatterOptions() {
  return quill::PatternFormatterOptions(
    "[%(time)][%(log_level_short_code)][%(logger)][%(file_name):%(line_number)] %(message)",
    "%Y-%m-%d %H:%M:%S.%Qns"
  );
}
