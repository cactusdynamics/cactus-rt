#include "cactus_rt/thread.h"

#include <cstring>
#include <stdexcept>

namespace cactus_rt {
template <typename SchedulerT>
void* Thread<SchedulerT>::RunThread(void* data) {
  auto* thread = static_cast<Thread*>(data);
  SchedulerT::SetThreadScheduling(thread->scheduler_config_);  // TODO: return error instead of throwing
  thread->BeforeRun();
  thread->Run();
  thread->AfterRun();
  return nullptr;
}

template <typename SchedulerT>
void Thread<SchedulerT>::Start(int64_t start_monotonic_time_ns) {
  start_monotonic_time_ns_ = start_monotonic_time_ns;

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

template <typename SchedulerT>
int Thread<SchedulerT>::Join() {
  return pthread_join(thread_, nullptr);
}
}  // namespace cactus_rt
