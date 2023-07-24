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

namespace cactus_rt {

using SchedulerConfigVariant = std::variant<OtherThreadConfig, FifoThreadConfig, DeadlineThreadConfig>;

/// @private
constexpr size_t kDefaultStackSize = 8 * 1024 * 1024;  // 8MB default stack space should be plenty

/**
 * The base thread
 */
class BaseThread {
  std::atomic_bool stop_requested_ = false;

 public:
  /**
   * @brief Return the name of the thread. Mostly used for debug purpose.
   *
   * @returns a const renferece to the name string
   */
  virtual const std::string& Name() = 0;

  /**
   * @brief Starts the thread.
   *
   * @param start_monotonic_time_ns The start time in the monotonic clock
   */
  virtual void Start(int64_t start_monotonic_time_ns) = 0;

  /**
   * @brief Joins the thread.
   *
   * @returns the return value of pthread_join.
   */
  virtual int Join() = 0;

  /**
   * Requests the thread to stop with an atomic.
   */
  virtual void RequestStop() noexcept {
    stop_requested_ = true;
  }

  // The constructors and destructors are needed because we need to delete
  // objects of type BaseThread polymorphically, through the map in the App class.
  BaseThread() = default;
  virtual ~BaseThread() = default;

  // Copy constructors are not allowed
  BaseThread(const BaseThread&) = delete;
  BaseThread& operator=(const BaseThread&) = delete;

  // Should the thread be moveable? std::thread is moveable
  // TODO: investigate moving the stop_requested_ flag somewhere else
  // Move constructors are not allowed because of the atomic_bool for now.
  BaseThread(BaseThread&&) noexcept = delete;
  BaseThread& operator=(BaseThread&&) noexcept = delete;

 protected:
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

class Thread : public BaseThread {
  std::string         name_;
  std::vector<size_t> cpu_affinity_;
  size_t              stack_size_;

  SchedulerConfigVariant scheduler_config_;

  quill::Logger* logger_;

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
      : name_(config.name),
        cpu_affinity_(config.cpu_affinity),
        stack_size_(static_cast<size_t>(PTHREAD_STACK_MIN) + config.stack_size),
        scheduler_config_(config.scheduler_config),
        logger_(quill::create_logger(name_)) {}

  /**
   * Returns the name of the thread
   *
   * @returns The name of the thread.
   */
  inline const std::string& Name() override {
    return name_;
  }

  /**
   * Starts the thread in the background.
   *
   * @param start_monotonic_time_ns should be the start time in nanoseconds for the monotonic clock.
   */
  void Start(int64_t start_monotonic_time_ns) override;

  /**
   * Joins the thread.
   *
   * @returns the return value of pthread_join
   */
  int Join() override;

 protected:
  inline quill::Logger*         Logger() const { return logger_; }
  inline SchedulerConfigVariant SchedulerConfig() {
    return scheduler_config_;
  }
  inline int64_t StartMonotonicTimeNs() const { return start_monotonic_time_ns_; }

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
};
}  // namespace cactus_rt

#endif
