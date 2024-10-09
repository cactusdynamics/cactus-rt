#include "cactus_rt/thread.h"

#include <sched.h>

#include <cerrno>
#include <cstring>
#include <ctime>
#include <memory>
#include <stdexcept>

#include "cactus_rt/config.h"
#include "cactus_rt/tracing/thread_tracer.h"
#include "quill/Frontend.h"
#include "quill/LogMacros.h"
#include "quill/Logger.h"
#include "quill/sinks/ConsoleSink.h"

namespace cactus_rt {

Thread::~Thread() {
  // Blocks until all messages up to the current timestamp are flushed on the
  // logger, to ensure every message is logged.
  this->Logger()->flush_log();
}

quill::Logger* Thread::CreateDefaultThreadLogger(std::string logger_name) {
  // TODO: (QUILL v7.3.0) move to another header file (cactus_rt/logging.h?)
  return quill::Frontend::create_or_get_logger(
    logger_name,
    quill::Frontend::create_or_get_sink<quill::ConsoleSink>(
      logger_name + "_ConsoleSink",  // Sink name is based on thread name
      true                           // Enable console colours
    ),
    quill::PatternFormatterOptions(
      "[%(time)][%(log_level_short_code)][%(logger)][%(file_name):%(line_number)] %(message)",
      "%Y-%m-%d %H:%M:%S.%Qns"
    )
  );
}

void* Thread::RunThread(void* data) {
  auto* thread = static_cast<Thread*>(data);

  if (!thread->created_by_app_) {
    throw std::runtime_error(std::string("do not create Thread manually, use App::CreateThread to create thread") + thread->name_);
  }

  thread->config_.scheduler->SetSchedAttr();

  pthread_setname_np(pthread_self(), thread->name_.c_str());

  thread->tracer_ = std::make_shared<tracing::ThreadTracer>(thread->name_, thread->config_.tracer_config.queue_size);
  thread->tracer_->SetTid();

  if (auto trace_aggregator = thread->trace_aggregator_.lock()) {
    trace_aggregator->RegisterThreadTracer(thread->tracer_);
  } else {
    LOG_WARNING(
      thread->Logger(),
      "thread {} does not have app_ and tracing is disabled for this thread. Did the App/Thread go out of scope before the thread is launched?",
      thread->name_
    );
  }

  quill::Frontend::preallocate();  // Pre-allocates thread-local data to avoid the need to allocate on the first log message

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
