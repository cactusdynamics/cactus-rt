#ifndef CACTUS_RT_APP_H_
#define CACTUS_RT_APP_H_

#include <gtest/gtest_prod.h>

#include <memory>
#include <string>
#include <vector>

#include "config.h"
#include "quill/Quill.h"
#include "thread.h"
#include "tracing/thread_tracer.h"
#include "tracing/trace_aggregator.h"

namespace cactus_rt {

/**
 * @brief Creates a real-time application with multiple real-time and non-real-time threads.
 */
class App {
  friend class Thread;
  FRIEND_TEST(SingleThreadTracingTest, QueueOverflowWillNotBlock);

  // The name of the app
  std::string name_;

  // Size of heap to reserve in bytes at program startup.
  size_t heap_size_;

  // Configuration for quill logging
  quill::Config logger_config_;

  TracerConfig tracer_config_;

  std::vector<std::shared_ptr<Thread>> threads_;

  std::shared_ptr<tracing::TraceAggregator> trace_aggregator_;

  void SetDefaultLogFormat(quill::Config& cfg) {
    // Create a handler of stdout
    const std::shared_ptr<quill::Handler> handler = quill::stdout_handler();

    // Enable console colours on the handler
    static_cast<quill::ConsoleHandler*>(handler.get())->enable_console_colours();

    // Set the default pattern
    handler->set_pattern("[%(ascii_time)][%(level_id)][%(logger_name)][%(filename):%(lineno)] %(message)", "%Y-%m-%d %H:%M:%S.%Qns");
    cfg.default_handlers.push_back(handler);
  }

 public:
  explicit App(std::string name = "RTApp", AppConfig config = AppConfig());

  virtual ~App();

  // Copy constructors
  App(const App&) = delete;
  App& operator=(const App&) = delete;

  // Move constructors
  App(App&&) noexcept = delete;
  App& operator=(App&&) noexcept = delete;

  /**
   * @brief Registers a thread to be automatically started by the app. The start
   * order of the threads are in the order of registration.
   *
   * @param thread A shared ptr to a thread.
   */
  void RegisterThread(std::shared_ptr<Thread> thread);

  /**
   * @brief Sets up the trace aggregator. Call this before starting the thread
   * if you don't want to call RegisterThread and maintain tracing capabilities.
   */
  void SetupTraceAggregator(Thread& thread);

  /**
   * @brief Starts the app by locking the memory and reserving the memory. Also
   * start all the threads in registration order.
   *
   * @param start_monotonic_time_ns The start time of the monotonic clock, if
   * you prefer to set a time. Mostly used for child class of App to keep a
   * consistent start time. Leave as default or pass -1 for the function to
   * automatically determine a time (i.e. most situations).
   */
  virtual void Start(int64_t start_monotonic_time_ns = -1);

  /**
   * @brief sends RequestStop to all threads in registration order.
   *
   * Provided for convenience only. If you want to stop in a different order,
   * you can override this method or implement your own functions.
   */
  virtual void RequestStop();

  /**
   * @brief Joins all the threads in registration order.
   *
   * Provided for convenience only. If you want to join in a different order,
   * you can override this method or implement your own functions.
   */
  virtual void Join();

  /**
   * @brief Starts a new tracing session for the process. Will not start a new
   * tracing session if an existing tracing session is in progress. This
   * function is not real-time safe.
   *
   * @param output_filename the filename the data will be written to.
   * @returns true if a session has started, false if a session is already in progress.
   */
  bool StartTraceSession(const char* output_filename) noexcept;

  /**
   * @brief Starts a new tracing session for the process. Will not start a new
   * tracing session if an existing tracing session is in progress. This
   * function is not real-time safe.
   */
  bool StartTraceSession(std::shared_ptr<tracing::Sink> sink) noexcept;

  /**
   * @brief Stops the tracing session for the process. Will be no-op if tracing
   * is not enabled. This function is not real-time safe.
   *
   * @returns true if a session was stopped, false if tracing is not enabled.
   */
  bool StopTraceSession() noexcept;

 protected:
  /**
   * Locks memory via mlockall and configure malloc to not give up memory nor
   * use mmap.
   */
  void LockMemory() const;

  /**
   * Reserve the heap based on the heap_size_.
   */
  void ReserveHeap() const;

  /**
   * Starts the Quill background logging thread.
   */
  void StartQuill();

 private:
  void StopTraceAggregator() noexcept;
};
}  // namespace cactus_rt

#endif
