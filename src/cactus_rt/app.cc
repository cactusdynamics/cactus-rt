#include "cactus_rt/app.h"

#include <malloc.h>
#include <sys/mman.h>

#include <cstring>
#include <stdexcept>

#include "cactus_rt/tracing/tracing_enabled.h"
#include "cactus_rt/utils.h"
#include "quill/Quill.h"

using FileSink = cactus_rt::tracing::FileSink;

namespace cactus_rt {

void App::RegisterThread(std::shared_ptr<Thread> thread) {
  threads_.push_back(thread);
}

App::App(std::string name, AppConfig config)
    : name_(name),
      heap_size_(config.heap_size),
      logger_config_(config.logger_config),
      tracer_config_(config.tracer_config) {
  if (logger_config_.default_handlers.empty()) {
    SetDefaultLogFormat(logger_config_);
  }

  // TODO: backend_thread_notification_handler can throw - we need to handle this somehow
  // logger_config_.backend_thread_notification_handler
}

App::~App() {
  StopTraceSession();
  quill::flush();
}

void App::Start() {
  LockMemory();
  ReserveHeap();
  StartQuill();

  auto start_monotonic_time_ns = NowNs();
  for (auto& thread : threads_) {
    thread->Start(start_monotonic_time_ns, trace_aggregator_);
  }
}

void App::RequestStop() {
  for (auto& thread : threads_) {
    thread->RequestStop();
  }
}

void App::Join() {
  for (auto& thread : threads_) {
    thread->Join();
  }
}

bool App::StartTraceSession(const char* output_filename) noexcept {
  if (cactus_rt::tracing::IsTracingEnabled()) {
    return false;
  }

  CreateAndStartTraceAggregator(std::make_shared<FileSink>(output_filename));
  cactus_rt::tracing::EnableTracing();

  return true;
}

bool App::StartTraceSession(std::shared_ptr<tracing::Sink> sink) noexcept {
  if (cactus_rt::tracing::IsTracingEnabled()) {
    return false;
  }

  CreateAndStartTraceAggregator(sink);
  cactus_rt::tracing::EnableTracing();

  return true;
}

void App::RegisterTraceSink(std::shared_ptr<tracing::Sink> sink) noexcept {
  const std::scoped_lock lock(aggregator_mutex_);

  if (trace_aggregator_ != nullptr) {
    trace_aggregator_->RegisterSink(sink);
  }
}

bool App::StopTraceSession() noexcept {
  if (!cactus_rt::tracing::IsTracingEnabled()) {
    return false;
  }

  cactus_rt::tracing::DisableTracing();
  StopTraceAggregator();

  return true;
}

void App::LockMemory() const {
  // See https://lwn.net/Articles/837019/

  // From the man page:
  //
  // Locks all pages mapped into the address space, including code, data, stack
  // segments, shared libraries, user space kernel data, shared memory, and
  // memory mapped files.
  //
  // All mapped pages are guaranteed to be resident in RAM when the call
  // returns successfully; the pages are guaranteed in RAM until later
  // unlocked.
  //
  // MCL_CURRENT: Lock all pages which are currently mapped into the address
  //              space of the process.
  //
  // MCL_FUTURE: Lock all pages which will become mapped into the address space
  //             of the process in the future. These could be, for instance,
  //             new pages required by a growing heap and stack as well as new
  //             memory mapped files and shared memory regions.
  int ret = mlockall(MCL_CURRENT | MCL_FUTURE);
  if (ret != 0) {
    throw std::runtime_error{std::string("mlockall failed: ") + std::strerror(errno)};
  }

  // Do not free any RAM to the OS if the contiguous free memory at the top of
  // the heap grows too large. If RAM is freed, a syscall (sbrk) will be called
  // which can have unbounded execution time.
  ret = mallopt(M_TRIM_THRESHOLD, -1);
  if (ret == 0) {
    // on error, errno is not set by mallopt
    throw std::runtime_error{"mallopt M_TRIM_THRESHOLD failed"};
  }

  // Do not allow mmap.
  // TODO: give example why this is bad for real-time.
  ret = mallopt(M_MMAP_MAX, 0);
  if (ret == 0) {
    throw std::runtime_error{"mallopt M_TRIM_THRESHOLD failed"};
  }
}

void App::ReserveHeap() const {
  if (heap_size_ == 0) {
    // Don't reserve anything
    return;
  }

  void* buf = malloc(heap_size_);
  if (buf == nullptr) {
    throw std::runtime_error{std::string("cannot malloc: ") + std::strerror(errno)};
  }

  // Contrary to many online resources, there is no need the poke each page in
  // the buffer to ensure that the page is actually allocated, because mlockall
  // effectively turns off demand paging. See mlockall(2) and "demand paging" on
  // Wikipedia. Also see:
  // https://github.com/ros2-realtime-demo/pendulum/issues/90#issuecomment-1105844726
  free(buf);
}

void App::StartQuill() {
  quill::configure(logger_config_);
  quill::start();
}

void App::CreateAndStartTraceAggregator(std::shared_ptr<tracing::Sink> sink) noexcept {
  const std::scoped_lock lock(aggregator_mutex_);

  if (trace_aggregator_ != nullptr) {
    // TODO: error here
    return;
  }

  trace_aggregator_ = std::make_shared<tracing::TraceAggregator>(name_, tracer_config_.trace_aggregator_cpu_affinity);
  for (auto tracer : thread_tracers_) {
    trace_aggregator_->RegisterThreadTracer(tracer);
  }

  if (sink != nullptr) {
    trace_aggregator_->RegisterSink(sink);
  }

  trace_aggregator_->Start();
}

void App::StopTraceAggregator() noexcept {
  const std::scoped_lock lock(aggregator_mutex_);

  if (trace_aggregator_ == nullptr) {
    // TODO: error here
    return;
  }

  trace_aggregator_->RequestStop();
  trace_aggregator_->Join();
  trace_aggregator_ = nullptr;
}
}  // namespace cactus_rt
