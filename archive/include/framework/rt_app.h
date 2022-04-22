#ifndef RT_DEMO_RT_APP_H_
#define RT_DEMO_RT_APP_H_

#include <boost/core/noncopyable.hpp>
#include <memory>
#include <vector>

#include "framework/thread.h"

namespace rt_demo::framework {
class RTApp : private boost::noncopyable {
  std::vector<Thread*> threads_;
  struct timespec      ref_time_;

 public:
  RTApp() {}
  virtual ~RTApp() = default;

  void AddThread(Thread* thread) {
    threads_.push_back(thread);
  }

  virtual void Start();
  virtual void Join();

 private:
  void LockMemory();
};
}  // namespace rt_demo::framework

#endif
