#ifndef RT_DEMO_THREAD_H_
#define RT_DEMO_THREAD_H_

#include <limits.h>
#include <pthread.h>
#include <sched.h>
#include <stdint.h>
#include <stdlib.h>
#include <time.h>

#include <boost/core/noncopyable.hpp>
#include <utility>

namespace rt_demo {
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

 public:
  Thread(int priority, int policy = SCHED_OTHER, uint32_t cpu_affinity = 0, size_t stack_size = 0);
  virtual ~Thread() {}

  void Start();
  int  Join();

 protected:
  virtual void Run() noexcept = 0;

  int64_t               NowNanoseconds() const noexcept;
  std::pair<long, long> GetPageFaultCount() const noexcept;
};
}  // namespace rt_demo

#endif
