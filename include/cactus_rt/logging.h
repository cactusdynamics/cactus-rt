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

/**
 * Create a ConsoleSink object with console colours.
 *
 * @param sink_name The Sink ID.
 * @return A pointer to the created sink. If a sink with that ID already
 * existed, a pointer to the existing sink is returned instead.
 */
std::shared_ptr<quill::Sink> DefaultConsoleSink(std::string sink_name);

/**
 * Get a default pattern format.
 */
quill::PatternFormatterOptions DefaultPatternFormatterOptions();

/**
 * Create a Logger object with default settings which will write logs to the
 * console with a default format.
 *
 * TODO: (QUILL v7.3.0): Make this use the `cactus_rt::Logger`
 * (`cactus_rt::BoundedDroppingLogger`) instead
 *
 * TODO: (QUILL v7.3.0): What happens if we pass in a logger name which already
 * exists? Are the sink and format discarded?
 *
 * @param logger_name
 * @return A pointer to the created logger. If a logger with that ID already
 * existed, a pointer to the existing logger is returned instead.
 */
cactus_rt::logging::Logger* DefaultLogger(std::string logger_name);

}  // namespace cactus_rt::logging

#endif
