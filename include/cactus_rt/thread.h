#ifndef CACTUS_RT_THREAD_H_
#define CACTUS_RT_THREAD_H_

#include <atomic>
#include <climits>  // For PTHREAD_STACK_MIN
#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>
#include <vector>

#include "config.h"
#include "quill/Quill.h"
#include "tracing/thread_tracer.h"
#include "tracing/trace_aggregator.h"

namespace cactus_rt {

/// @private
constexpr size_t kDefaultStackSize = 8 * 1024 * 1024;  // 8MB default stack space should be plenty

// Necessary forward declaration
class App;

class Thread {
  ThreadConfig        config_;
  std::string         name_;
  std::vector<size_t> cpu_affinity_;
  size_t              stack_size_;

  quill::Logger*                         logger_;
  std::shared_ptr<tracing::ThreadTracer> tracer_;

  std::atomic_bool stop_requested_ = false;

  // Non-owning App pointer. Used only for notifying that the thread has
  // started/stopped for tracing purposes.
  App* app_ = nullptr;

  pthread_t thread_;
  int64_t   start_monotonic_time_ns_ = 0;

  /**
   * A wrapper function that is passed to pthreads which starts the thread and
   * performs necessary setup for RT.
   */
  static void* RunThread(void* data);

 public:
  /**
   * Creates a new thread.
   *
   * @param config The configuration for the thread
   */
  Thread(ThreadConfig config)
      : config_(config),
        name_(config_.name),
        cpu_affinity_(config_.cpu_affinity),
        stack_size_(static_cast<size_t>(PTHREAD_STACK_MIN) + config_.stack_size),
        logger_(quill::create_logger(name_)),
        tracer_(std::make_shared<tracing::ThreadTracer>(config_.name, config_.tracer_config.queue_size)) {}

  /**
   * Returns the name of the thread
   *
   * @returns The name of the thread.
   */
  inline const std::string& Name() { return name_; }

  /**
   * Starts the thread in the background.
   *
   * @param start_monotonic_time_ns should be the start time in nanoseconds for the monotonic clock.
   */
  void Start(int64_t start_monotonic_time_ns);

  /**
   * Joins the thread.
   *
   * @returns the return value of pthread_join
   */
  int Join();

  /**
   * Requests the thread to stop with an atomic.
   */
  virtual void RequestStop() noexcept {
    stop_requested_ = true;
  }

  /**
   * @brief Sets the trace_aggregator_ pointer so the thread can notify the
   *        trace_aggregator_ when it starts. This should only be called by App.
   *
   * @private
   */
  inline void SetApp(App* app) {
    app_ = app;
  }

  // The constructors and destructors are needed because we need to delete
  // objects of type Thread polymorphically, through the map in the App class.
  Thread() = default;
  virtual ~Thread() = default;

  // Copy constructors are not allowed
  Thread(const Thread&) = delete;
  Thread& operator=(const Thread&) = delete;

  // Should the thread be moveable? std::thread is moveable
  // TODO: investigate moving the stop_requested_ flag somewhere else
  // Move constructors are not allowed because of the atomic_bool for now.
  Thread(Thread&&) noexcept = delete;
  Thread& operator=(Thread&&) noexcept = delete;

 protected:
  inline quill::Logger*         Logger() const { return logger_; }
  inline tracing::ThreadTracer& Tracer() { return *tracer_; }
  inline int64_t                StartMonotonicTimeNs() const { return start_monotonic_time_ns_; }
  inline const ThreadConfig&    Config() const { return config_; }

  /**
   * Override this method to do work. If this is a real-time thread, once this
   * method is entered, the code in it should be RT-compatible.
   */
  virtual void Run() = 0;

  /**
   * Called before Run gets called. If the thread is real-time, this is likely
   * not a real-time section.
   */
  virtual void BeforeRun() {}

  /**
   * Called after Run returns. If the thread is real-time, this is likely not a
   * real-time section.
   */
  virtual void AfterRun() {}

  /**
   * @brief Check if stop has been requested
   *
   * @return true if stop is requested
   */
  bool StopRequested() const noexcept {
    // Memory order relaxed is OK, because we don't really care when the signal
    // arrives, we just care that it is arrived at some point.
    //
    // Also this could be used in a tight loop so we don't want to waste time when we don't need to.
    //
    // https://stackoverflow.com/questions/70581645/why-set-the-stop-flag-using-memory-order-seq-cst-if-you-check-it-with-memory
    // TODO: possibly use std::stop_source and std::stop_token (C++20)
    return stop_requested_.load(std::memory_order_relaxed);
  }
};
}  // namespace cactus_rt

#endif
