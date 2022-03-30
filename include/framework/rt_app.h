#ifndef RT_DEMO_RT_APP_H_
#define RT_DEMO_RT_APP_H_

#include <boost/core/noncopyable.hpp>
#include <memory>
#include <vector>

#include "framework/thread.h"

namespace rt_demo::framework {
class RTApp : private boost::noncopyable {
  std::vector<std::unique_ptr<Thread>> threads_;
  struct timespec                      ref_time_;

 public:
  RTApp() {}

  void AddThread(std::unique_ptr<Thread> thread) {
    threads_.push_back(std::move(thread));
  }

  void Start();
  void Join();

 private:
  void LockMemory();
};
}  // namespace rt_demo::framework

#endif
