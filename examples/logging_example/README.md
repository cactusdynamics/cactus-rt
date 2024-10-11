`logging_example`
================

A simple example showing how to configure logging. Cactus RT uses [Quill](https://github.com/odygrd/quill) as a logger. Read the [Quill documentation](https://quillcpp.readthedocs.io/en/latest/) for details and additional examples.

## `cactus_rt/logging.h`

To use Quill in a real-time friendly manner, `include/cactus_rt/logging.h` defines important types, default settings and utilities.

**Important**: `cactus_rt::logging::Logger` and `cactus_rt::logging::Frontend` types which define a `quill::QueueType::BoundedDropping` queue to prevent delays in case the loggers overflow, which is essential in any real-time thread. These *must* be used throughout the application instead of the default `quill::Logger` and `quill::Frontend` types!

## Logging non-primitive STL types

Logging non-primitive types on the hot path (i.e. in a real-time thread) requires some additional work. Most often-used standard library types are already provided for you by Quill though, and only require a simple `#include`.

For example, when logging `std::chrono` types, you need to insert the following:

```cpp
#include "quill/LogMacros.h"
// Required to parse std::chrono inside logging macros
#include "quill/std/Chrono.h"  // IWYU pragma: keep

...

LOG_INFO(logger, "Time: {}", std::chrono::seconds(3));
```

The [Quill Cheat Sheet](https://quillcpp.readthedocs.io/en/latest/cheat_sheet.html#) contains very useful information for logging various non-primitive types.

## Default logging

If unspecified, each thread will create a default logger for itself. This logger will write to a default console sink and uses a default format. All of these defaults can be found in `include/cactus_rt/logging.h`.

## Customize logger, sink(s) or pattern format

Customization of the quill Backend worker thread can be done by passing in logging options to the `cactus_rt::AppConfig`.

To use a custom sink or pattern format, define them before creating the logger. The sink(s) and pattern format are used to create the logger. Finally, the name of the created logger must be passed to the `cactus_rt::ThreadConfig`.

The snippets below might help

1. Create a sink (see the [Quill documentation on sink types](https://quillcpp.readthedocs.io/en/latest/sink_types.html) for the full code to create each sink).

   ```cpp
   // Default console sink
   auto console_sink = cactus_rt::logging::DefaultConsoleSink();

   // Custom sink, e.g. a file sink
   // !! Make sure to use `cactus_rt::logging::Frontend instead of quill::Frontend !!
   auto file_sink = cactus_rt::logging::Frontend::create_or_get_sink<quill::FileSink>(...);
   ```

2. Create a pattern format

   ```cpp
   // Default formatter pattern
   auto pattern_format = cactus_rt::logging::DefaultPatternFormatterOptions();

   // Custom formatter pattern
   auto pattern_format = quill::PatternFormatterOptions(...);
   ```

3. Create the logger

   ```cpp
   // Create custom logger using a single sink
   // !! Make sure to use `cactus_rt::logging::Frontend instead of quill::Frontend !!
   auto* custom_logger = cactus_rt::logging::Frontend::create_or_get_logger("CustomLogger", console_sink, pattern_format);

   // Alternatively, you can add multiple sinks to a vector and pass that instead
   const std::vector<std::shared_ptr<quill::Sink>> sinks = {console_sink, file_sink};
   // !! Make sure to use `cactus_rt::logging::Frontend instead of quill::Frontend !!
   auto* custom_logger = cactus_rt::logging::Frontend::create_or_get_logger("CustomLogger", sinks, pattern_format);
   ```

4. Pass the logger to the thread

   ```cpp
   // Add the custom logger name to the thread config
   cactus_rt::ThreadConfig thread_config;
   thread_config.logger_name = custom_logger->get_logger_name();

   // Finally, create the thread with using the thread config
   auto thread = app.CreateThread<ExampleRTThread>("ExampleRTThread", thread_config);
   ```
