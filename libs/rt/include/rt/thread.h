#ifndef RT_DEMO_RT_THREAD_H_
#define RT_DEMO_RT_THREAD_H_

#include <limits.h>  // For PTHREAD_STACK_MIN
#include <pthread.h>
#include <sched.h>
#include <sys/resource.h>  // needed for getrusage
#include <sys/time.h>      // needed for getrusage

#include <cstdint>
#include <string>

namespace rt {

constexpr size_t kDefaultStackSize = 8 * 1024 * 1024;  // 8MB

class Thread {
  std::string name_;
  int         priority_;
  int         policy_;
  uint32_t    cpu_affinity_;
  size_t      stack_size_;

  pthread_t thread_;

  int64_t start_monotonic_time_ns_ = 0;

  // Debug information
  int64_t       start_wall_time_ns_ = 0;
  struct rusage page_faults_at_start_;

  /**
   * A wrapper function that is passed to pthread. This starts the thread and
   * performs any necessary setup.
   */
  static void* RunThread(void* data);

  static void ReserveStackForThread();

 public:
  Thread(const std::string& name,
         int                priority,
         int                policy = SCHED_OTHER,
         uint32_t           cpu_affinity = 0,
         size_t             stack_size = kDefaultStackSize)
      : name_(name),
        priority_(priority),
        policy_(policy),
        cpu_affinity_(cpu_affinity),
        // In case stack_size is 0...
        stack_size_(PTHREAD_STACK_MIN + stack_size){};

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
  void Start(int64_t start_monotonic_time_ns, int64_t start_wall_time_ns);

  /**
   * Joins the thread.
   *
   * @returns the return value of pthread_join
   */
  int Join();

  /**
   * The name of the thread.
   */
  const std::string& Name() const { return name_; }

 protected:
  /**
   * Override this method to do work. If this is a real-time thread, once this
   * method is entered, the code in it should be RT-compatible.
   */
  virtual void Run() noexcept = 0;

  /**
   * Called before Run gets called. Non-RT.
   */
  virtual void BeforeRun() {}

  /**
   * Called after Run returns. Non-RT.
   */
  virtual void AfterRun() {}
};
}  // namespace rt

#endif
