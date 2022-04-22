#include "framework/thread.h"

#include <spdlog/spdlog.h>
#include <sys/resource.h>  // needed for getrusage
#include <sys/time.h>      // needed for getrusage
#include <unistd.h>

#include <stdexcept>

#include "rt_demo_sdt.h"

namespace rt_demo::framework {

void* Thread::RunThread(void* data) {
  Thread* thread = static_cast<Thread*>(data);

  if (thread->policy_ == SCHED_FIFO || thread->policy_ == SCHED_DEADLINE) {
    // This is a real time thread
    // TODO: additional logging?
  }

  thread->BeforeRun();

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

  thread->AfterRun();

  return NULL;
}

Thread::Thread(const std::string& name, int priority,
               int policy, uint32_t cpu_affinity,
               size_t stack_size) : priority_(priority),
                                    policy_(policy),
                                    cpu_affinity_(cpu_affinity),
                                    stack_size_(stack_size),
                                    name_(name) {
}

void Thread::Start(const struct timespec& ref_time) {
  // TODO: prevent multiple calls to Start
  ref_time_ = ref_time;

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

struct timespec Thread::Now() const noexcept {
  // Confused about move or copy?
  // https://gist.github.com/shuhaowu/916d1a1f3096f4b5f38edc635f612992
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts;
}

std::pair<long, long> Thread::GetPageFaultCount() const noexcept {
  std::pair<long, long> page_faults;

  struct rusage usage;
  getrusage(RUSAGE_THREAD, &usage);

  page_faults.first = usage.ru_minflt;
  page_faults.second = usage.ru_majflt;

  return page_faults;
}

}  // namespace rt_demo::framework
