#ifndef RT_DEMO_THREAD_H_
#define RT_DEMO_THREAD_H_

#include <limits.h>
#include <pthread.h>
#include <sched.h>
#include <stdint.h>
#include <stdlib.h>
#include <time.h>

#include <boost/core/noncopyable.hpp>
#include <string>
#include <utility>

namespace rt_demo::framework {
class Thread : private boost::noncopyable {
  int      priority_;
  int      policy_;
  uint32_t cpu_affinity_;
  size_t   stack_size_;

  pthread_t thread_;

  // Debug information
  long soft_page_fault_count_at_start_;
  long hard_page_fault_count_at_start_;

  // A wrapper function so the Run() Function can be called from pthread.
  static void* RunThread(void* data);

 protected:
  struct timespec ref_time_;
  std::string     name_;

 public:
  // According to sched_setscheduler(2), priority must be 0 if policy is SCHED_OTHER
  Thread(const std::string& name, int priority, int policy = SCHED_OTHER, uint32_t cpu_affinity = 0, size_t stack_size = 8 * 1024 * 1024);
  // TODO: need a defaulted move constructor. See https://en.cppreference.com/w/cpp/language/rule_of_three (rule of five).
  virtual ~Thread() = default;

  /**
   * Start the pthread.
   *
   * @param ref_time The start time which is used as a reference to compute timestamp for all the data.
   */
  void Start(const struct timespec& ref_time);
  int  Join();

  const std::string& Name() { return name_; };

 protected:
  virtual void Run() noexcept = 0;

  struct timespec       Now() const noexcept;
  std::pair<long, long> GetPageFaultCount() const noexcept;
};
}  // namespace rt_demo::framework

#endif
