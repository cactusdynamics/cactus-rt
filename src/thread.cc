#include "thread.h"

#include <spdlog/spdlog.h>
#include <sys/resource.h>  // needed for getrusage
#include <sys/time.h>      // needed for getrusage

#include <stdexcept>

#include "rt_demo_sdt.h"

namespace rt_demo {

void* Thread::RunThread(void* data) {
  Thread* thread = static_cast<Thread*>(data);

  if (thread->policy_ == SCHED_FIFO || thread->policy_ == SCHED_DEADLINE) {
    spdlog::debug("starting RT thread at pid {}", getpid());
  }

  // Get the starting page fault count
  auto page_faults = thread->GetPageFaultCount();
  thread->soft_page_fault_count_at_start_ = page_faults.first;
  thread->hard_page_fault_count_at_start_ = page_faults.second;

  RT_DEMO_THREAD_START(thread->policy_, page_faults.first, page_faults.second);

  thread->Run();

  page_faults = thread->GetPageFaultCount();
  auto soft_page_fault_diff = page_faults.first - thread->soft_page_fault_count_at_start_;
  auto hard_page_fault_diff = page_faults.second - thread->hard_page_fault_count_at_start_;

  RT_DEMO_THREAD_DONE(thread->policy_, page_faults.first, page_faults.second);

  spdlog::debug("Thread exitted with {} minor faults and {} major faults", soft_page_fault_diff, hard_page_fault_diff);

  return NULL;
}

Thread::Thread(int priority, int policy, uint32_t cpu_affinity,
               size_t stack_size) : priority_(priority),
                                    policy_(policy),
                                    cpu_affinity_(cpu_affinity),
                                    stack_size_(stack_size) {
}

void Thread::Start() {
  int            ret;
  pthread_attr_t attr;

  // Initialize the pthread attribute
  ret = pthread_attr_init(&attr);
  if (ret) {
    throw std::runtime_error("error in pthread_attr_init: " + std::to_string(ret));
  }

  // Set a stack size
  ret = pthread_attr_setstacksize(&attr, stack_size_);
  if (ret) {
    throw std::runtime_error("error in pthread_attr_setstacksize: " + std::to_string(ret));
  }

  // Set the scheduler policy
  ret = pthread_attr_setschedpolicy(&attr, policy_);
  if (ret) {
    throw std::runtime_error("error in pthread_attr_setschedpolicy: " + std::to_string(ret));
  }

  // Set the scheduler priority
  struct sched_param param;
  param.sched_priority = priority_;
  ret = pthread_attr_setschedparam(&attr, &param);
  if (ret) {
    throw std::runtime_error("error in pthread_attr_setschedparam: " + std::to_string(ret));
  }

  // Make sure threads created using the thread_attr_ takes the value from the attribute instead of inherit from the parent thread.
  ret = pthread_attr_setinheritsched(&attr, PTHREAD_EXPLICIT_SCHED);
  if (ret) {
    throw std::runtime_error("error in pthread_attr_setinheritsched: " + std::to_string(ret));
  }

  ret = pthread_create(&thread_, &attr, &Thread::RunThread, this);
  if (ret) {
    throw std::runtime_error("error in pthread_create: " + std::to_string(ret));
  }
}

int Thread::Join() {
  return pthread_join(thread_, NULL);
}

int64_t Thread::NowNanoseconds() const noexcept {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  int64_t ns = ts.tv_nsec;
  ns += ts.tv_sec * 1'000'000'000;
  return ns;
}

std::pair<long, long> Thread::GetPageFaultCount() const noexcept {
  std::pair<long, long> page_faults;

  struct rusage usage;
  getrusage(RUSAGE_THREAD, &usage);

  page_faults.first = usage.ru_minflt;
  page_faults.second = usage.ru_majflt;

  return page_faults;
}

}  // namespace rt_demo
