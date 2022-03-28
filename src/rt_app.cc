#include "rt_app.h"

#include <malloc.h>
#include <spdlog/spdlog.h>
#include <sys/mman.h>

#include <stdexcept>

namespace rt_demo {
void RTApp::Start() {
  spdlog::info("Starting RTApp");
  LockMemory();
  for (const auto& thread : threads_) {
    thread->Start();
  }
}

void RTApp::Join() {
  for (const auto& thread : threads_) {
    thread->Join();
  }
}

void RTApp::LockMemory() {
  // See https://lwn.net/Articles/837019/
  int ret;
  ret = mlockall(MCL_CURRENT | MCL_FUTURE);
  if (ret) {
    throw std::runtime_error{"mlockall failed: " + std::to_string(ret)};
  }

  // Do not free any RAM to the OS if the continguous free memory at the top of
  // the heap grows large.
  ret = mallopt(M_TRIM_THRESHOLD, -1);
  if (ret == 0) {
    throw std::runtime_error{"mallopt M_TRIM_THRESHOLD failed"};
  }

  // Do not allow mmap.
  // TODO: give example why this is bad.
  ret = mallopt(M_MMAP_MAX, 0);
  if (ret == 0) {
    throw std::runtime_error{"mallopt M_TRIM_THRESHOLD failed"};
  }

  // TODO: is prefaulting needed? https://github.com/ros2-realtime-demo/pendulum/issues/90
}
}  // namespace rt_demo
