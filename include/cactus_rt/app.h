#ifndef CACTUS_RT_APP_H_
#define CACTUS_RT_APP_H_

#include <gtest/gtest_prod.h>

#include <memory>
#include <string>
#include <vector>

#include "config.h"
#include "logger.h"
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
  LoggerConfig logger_config_;

  TracerConfig tracer_config_;

  std::shared_ptr<tracing::TraceAggregator> trace_aggregator_;  // Must be above threads_ to guarantee destructor order.

  std::vector<std::shared_ptr<Thread>> threads_;

 public:
  explicit App(std::string name = "RTApp", AppConfig config = AppConfig());

  virtual ~App();

  // Copy constructors
  App(const App&) = delete;
  App& operator=(const App&) = delete;

  // Move constructors
  App(App&&) noexcept = delete;
  App& operator=(App&&) noexcept = delete;

  cactus_rt::Logger* CreateLogger(const std::string& name) const;

  template <typename ThreadT, typename... Args>
  std::shared_ptr<ThreadT> CreateThread(Args&&... args) {
    static_assert(std::is_base_of_v<Thread, ThreadT>, "Must derive from cactus_rt::Thread");
    std::shared_ptr<ThreadT> thread = std::make_shared<ThreadT>(std::forward<Args>(args)...);

    Thread* base_thread = thread.get();
    base_thread->trace_aggregator_ = trace_aggregator_;
    base_thread->created_by_app_ = true;
    base_thread->logger_ = CreateLogger(base_thread->name_);

    threads_.push_back(thread);

    return thread;
  }

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
  void StartQuill() const;

 private:
  void StopTraceAggregator() noexcept;
};
}  // namespace cactus_rt

#endif
