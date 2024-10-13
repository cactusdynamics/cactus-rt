#ifndef CACTUS_RT_LOGGING_H_
#define CACTUS_RT_LOGGING_H_

#include <cstdint>
#include <memory>
#include <string>

#include "quill/Frontend.h"
#include "quill/Logger.h"
#include "quill/backend/BackendOptions.h"
#include "quill/core/Common.h"
#include "quill/core/PatternFormatterOptions.h"
#include "quill/sinks/Sink.h"

// The quill logging macros are explicitly included in this header file.
// This is convenience to prevent another #include when using cactus_rt logging.
#include "quill/LogMacros.h"  // IWYU pragma: export

namespace cactus_rt::logging {
/**
 * Defines a Bounded Dropping queue, to drop logging messages if the buffers
 * fill up. This prevents run-time reallocations.

 * FrontendOptions are compile-time options and must be passed as a
 * template argument.
 *
 * Based on:
 * - https://github.com/odygrd/quill/blob/v7.3.0/examples/custom_frontend_options.cpp
 * - https://quillcpp.readthedocs.io/en/latest/frontend_options.html
 */
struct BoundedDroppingFrontendOptions {
  static constexpr quill::QueueType queue_type = quill::QueueType::BoundedDropping;
  static constexpr uint32_t         initial_queue_capacity = 128 * 1024;     // 128 KiB
  static constexpr uint32_t         blocking_queue_retry_interval_ns = 800;  // Ignored for Dropping queue
  static constexpr bool             huge_pages_enabled = false;
};

/// Type alias for `BoundedDroppingFrontendOptions`
using FrontendOptions = BoundedDroppingFrontendOptions;

/**
 * Define a quill::Frontend class using the custom options. This Frontend must
 * be used consistently throughout the application instead of the default
 * `quill::Frontend`.
 *
 * FrontendOptions are compile-time options and must be passed as a template
 * argument.
 */
using BoundedDroppingFrontend = quill::FrontendImpl<BoundedDroppingFrontendOptions>;

/// Type alias for `BoundedDroppingFrontend`
using Frontend = BoundedDroppingFrontend;

/**
 * Define a custom quill::Logger to also use the custom options. This Logger
 * must be used consistently throughout the application instead of the default
 * `quill::Logger`.
 *
 * FrontendOptions are compile-time options and must be passed as a template
 * argument.
 */
using BoundedDroppingLogger = quill::LoggerImpl<BoundedDroppingFrontendOptions>;

/// Type alias for `BoundedDroppingLogger`
using Logger = BoundedDroppingLogger;

/**
 * Sets `quill:BackendOptions` to suitable defaults for real-time logging.
 *
 * @return quill::BackendOptions
 */
quill::BackendOptions DefaultBackendOptions();

std::string DefaultConsoleSinkName();

/**
 * Create a default ConsoleSink object with console colours. The name of this
 * sink is defined by `cactus_rt::logging::DefaultConsoleSinkName()`.
 *
 * @note If this is not the first call to this function, a pointer to the
 * existing default console sink is returned instead of creating a new one.
 *
 * @return A pointer to the sink.
 */
std::shared_ptr<quill::Sink> DefaultConsoleSink();

/**
 * Get a default pattern format.
 */
quill::PatternFormatterOptions DefaultPatternFormatterOptions();

/**
 * Create or get a Logger object with default settings which will write logs to
 * the console with a default format.
 *
 * @param logger_name The logger name to use.
 * @return A pointer to the created logger. If a logger with that name already
 * existed, a pointer to the existing logger is returned instead.
 */
cactus_rt::logging::Logger* DefaultLogger(std::string logger_name);

}  // namespace cactus_rt::logging

#endif
