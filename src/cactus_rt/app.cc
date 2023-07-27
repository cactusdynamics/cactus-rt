#include "cactus_rt/app.h"

#include <malloc.h>
#include <sys/mman.h>

#include <cstring>
#include <stdexcept>

#include "cactus_rt/tracing/sink.h"
#include "cactus_rt/utils.h"
#include "quill/Quill.h"

using Sink = cactus_rt::tracing::Sink;
using FileSink = cactus_rt::tracing::FileSink;

namespace cactus_rt {

void App::RegisterThread(std::shared_ptr<BaseThread> thread) {
  threads_.push_back(thread);

  // TODO: queue length... This needs thread config refactor
  thread->RegisterThreadTracer(tracer_.CreateThreadTracer(thread->Name().c_str()));
}

App::App(const AppConfig& config)
    : name_(config.name),
      heap_size_(config.reserved_heap_size),
      tracer_(config.name, config.tracer_cpu_affinity_) {
  if (config.logger_config == std::nullopt) {
    quill::Config default_config;

    // TODO: backend_thread_notification_handler can throw - we need to handle this somehow
    // default_config.backend_thread_notification_handler

    SetDefaultLogFormat(default_config);
    logger_config_ = default_config;
  } else {
    logger_config_ = config.logger_config.value();
    if (logger_config_.default_handlers.empty()) {
      SetDefaultLogFormat(logger_config_);
    }
  }

  // TODO: deal with logger background thread CPU affinity
  tracer_.RegisterSink(std::make_unique<FileSink>("data.perfetto"));
}

void App::Start() {
  LockMemory();
  ReserveHeap();
  StartQuill();

  auto start_monotonic_time_ns = NowNs();
  tracer_.Start(start_monotonic_time_ns);

  for (auto& thread : threads_) {
    thread->Start(start_monotonic_time_ns);
  }
}

void App::RequestStop(bool stop_system_threads_only) {
  if (!stop_system_threads_only) {
    for (auto& thread : threads_) {
      thread->RequestStop();
    }
  }

  tracer_.RequestStop();
}

void App::Join(bool join_system_threads_only) {
  if (!join_system_threads_only) {
    for (auto& thread : threads_) {
      thread->Join();
    }
  }

  tracer_.Join();
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

  // Do not free any RAM to the OS if the continguous free memory at the top of
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
}  // namespace cactus_rt
