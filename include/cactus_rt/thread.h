#ifndef CACTUS_RT_THREAD_H_
#define CACTUS_RT_THREAD_H_

#include <limits.h>  // For PTHREAD_STACK_MIN
#include <pthread.h>

#include <cstring>
#include <stdexcept>
#include <string>
#include <vector>

#include "linux/sched_ext.h"

namespace cactus_rt {

constexpr size_t kDefaultStackSize = 8 * 1024 * 1024;  // 8MB

// TODO: some docs
template <typename SchedulerT>
class Thread {
  std::string                 name_;
  typename SchedulerT::Config scheduler_config_;
  pthread_t                   thread_;
  std::vector<size_t>         cpu_affinity_;
  size_t                      stack_size_;

  int64_t start_monotonic_time_ns_ = 0;
  int64_t start_wall_time_ns_ = 0;

  /**
   * A wrapper function that is passed to pthread. This starts the thread and
   * performs any necessary setup.
   */
  static void* RunThread(void* data) {
    auto* thread = static_cast<Thread*>(data);
    SchedulerT::SetThreadScheduling(thread->scheduler_config_);  // TODO: return error instead of throwing
    thread->BeforeRun();
    thread->Run();
    thread->AfterRun();
    return nullptr;
  }

 public:
  Thread(const std::string&                 name,
         const typename SchedulerT::Config& config = {},
         std::vector<size_t>                cpu_affinity = {},
         size_t                             stack_size = kDefaultStackSize)
      : name_(name), scheduler_config_(config), cpu_affinity_(cpu_affinity),
        // In case stack_size is 0...
        stack_size_(static_cast<size_t>(PTHREAD_STACK_MIN) + stack_size){};

  virtual ~Thread() = default;

  // Copy constructors
  Thread(const Thread&) = delete;
  Thread& operator=(const Thread&) = delete;

  // Move constructors
  Thread(Thread&&) noexcept = default;
  Thread& operator=(Thread&&) noexcept = default;

  /**
   * Starts the thread in the background.
   *
   * @param start_monotonic_time_ns should be the start time in nanoseconds for the monotonic clock.
   * @param start_wall_time_ns should be the start time in nanoseconds for the realtime clock.
   */

  void Start(int64_t start_monotonic_time_ns, int64_t start_wall_time_ns) {
    start_monotonic_time_ns_ = start_monotonic_time_ns;
    start_wall_time_ns_ = start_wall_time_ns;

    pthread_attr_t attr;

    // Initialize the pthread attribute
    int ret = pthread_attr_init(&attr);
    if (ret != 0) {
      throw std::runtime_error(std::string("error in pthread_attr_init: ") + std::strerror(ret));
    }

    // Set a stack size
    //
    // Note the stack is prefaulted if mlockall(MCL_FUTURE | MCL_CURRENT) is
    // called, which under this app framework should be.
    //
    // Not even sure if there is an optimizer-safe way to prefault the stack
    // anyway, as the compiler optimizer may realize that buffer is never used
    // and thus will simply optimize it out.
    ret = pthread_attr_setstacksize(&attr, stack_size_);
    if (ret != 0) {
      throw std::runtime_error(std::string("error in pthread_attr_setstacksize: ") + std::strerror(ret));
    }

    // Setting CPU mask
    if (!cpu_affinity_.empty()) {
      cpu_set_t cpuset;
      CPU_ZERO(&cpuset);
      for (auto cpu : cpu_affinity_) {
        CPU_SET(cpu, &cpuset);
      }

      ret = pthread_attr_setaffinity_np(&attr, sizeof(cpu_set_t), &cpuset);
      if (ret != 0) {
        throw std::runtime_error(std::string("error in pthread_attr_setaffinity_np: ") + std::strerror(ret));
      }
    }

    ret = pthread_create(&thread_, &attr, &Thread<SchedulerT>::RunThread, this);
    if (ret != 0) {
      throw std::runtime_error(std::string("error in pthread_create: ") + std::strerror(ret));
    }
  }

  /**
   * Joins the thread.
   *
   * @returns the return value of pthread_join
   */
  int Join() const {
    return pthread_join(thread_, nullptr);
  }

 protected:
  int64_t StartMonotonicTimeNs() const { return start_monotonic_time_ns_; }
  int64_t StartWallTimeNs() const { return start_wall_time_ns_; }

  /**
   * Override this method to do work. If this is a real-time thread, once this
   * method is entered, the code in it should be RT-compatible.
   */
  virtual void Run() = 0;

  /**
   * Called before Run gets called. Non-RT.
   */
  virtual void BeforeRun() {}

  /**
   * Called after Run returns. Non-RT.
   */
  virtual void AfterRun() {}
};
}  // namespace cactus_rt

#endif