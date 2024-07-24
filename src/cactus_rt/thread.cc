#include "cactus_rt/thread.h"

#include <sched.h>

#include <cerrno>
#include <cstring>
#include <ctime>
#include <memory>
#include <stdexcept>

#include "cactus_rt/config.h"
#include "cactus_rt/tracing/thread_tracer.h"

namespace cactus_rt {

void* Thread::RunThread(void* data) {
  auto* thread = static_cast<Thread*>(data);
  thread->config_.scheduler->SetSchedAttr();

  thread->tracer_ = std::make_shared<tracing::ThreadTracer>(thread->name_, thread->config_.tracer_config.queue_size);
  thread->tracer_->SetTid();

  if (auto trace_aggregator = thread->trace_aggregator_.lock()) {
    trace_aggregator->RegisterThreadTracer(thread->tracer_);
  } else {
    LOG_WARNING(thread->Logger(), "thread {} does not have app_ and tracing is disabled for this thread. Did you call App::RegisterThread?", thread->name_);
  }

  quill::preallocate();  // Pre-allocates thread-local data to avoid the need to allocate on the first log message

  thread->BeforeRun();
  thread->Run();
  thread->AfterRun();

  thread->tracer_->MarkDone();
  thread->tracer_ = nullptr;

  return nullptr;
}

void Thread::Start(int64_t start_monotonic_time_ns) {
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

  ret = pthread_create(&thread_, &attr, &Thread::RunThread, this);
  if (ret != 0) {
    throw std::runtime_error(std::string("error in pthread_create: ") + std::strerror(ret));
  }
}

int Thread::Join() const {
  return pthread_join(thread_, nullptr);
}
}  // namespace cactus_rt
