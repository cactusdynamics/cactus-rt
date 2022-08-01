#include <pthread.h>
#include <sys/mman.h>  // necessary for mlockall

#include <cstring>
#include <ctime>  // For timespec
#include <stdexcept>
#include <string>

// DO NOT USE THIS CODE. DEMONSTRATION ONLY.
// See https://shuhaowu.com/blog/2022/04-linux-rt-appdev-part4.html
// Instead, use cactus_rt::Thread.

class Thread {
  int priority_;
  int policy_;

  int64_t         period_ns_;
  struct timespec next_wakeup_time_;

  pthread_t thread_;

  static void* RunThread(void* data) {
    Thread* thread = static_cast<Thread*>(data);
    thread->Run();
    return NULL;
  }

 public:
  Thread(int priority, int policy, int64_t period_ns = 1'000'000)
      : priority_(priority), policy_(policy), period_ns_(period_ns) {}
  virtual ~Thread() = default;

  // Delete the copy constructor; default the move constructor...

  void Start() {
    pthread_attr_t attr;

    // Initialize the pthread attribute
    int ret = pthread_attr_init(&attr);
    if (ret) {
      throw std::runtime_error(std::string("error in pthread_attr_init: ") + std::strerror(ret));
    }

    // Set the scheduler policy
    ret = pthread_attr_setschedpolicy(&attr, policy_);
    if (ret) {
      throw std::runtime_error(std::string("error in pthread_attr_setschedpolicy: ") + std::strerror(ret));
    }

    // Set the scheduler priority
    struct sched_param param;
    param.sched_priority = priority_;
    ret = pthread_attr_setschedparam(&attr, &param);
    if (ret) {
      throw std::runtime_error(std::string("error in pthread_attr_setschedparam: ") + std::strerror(ret));
    }

    // Make sure threads created using the thread_attr_ takes the value from the attribute instead of inherit from the parent thread.
    ret = pthread_attr_setinheritsched(&attr, PTHREAD_EXPLICIT_SCHED);
    if (ret) {
      throw std::runtime_error(std::string("error in pthread_attr_setinheritsched: ") + std::strerror(ret));
    }

    ret = pthread_create(&thread_, &attr, &Thread::RunThread, this);
    if (ret) {
      throw std::runtime_error(std::string("error in pthread_create: ") + std::strerror(ret));
    }
  }

  int Join() {
    return pthread_join(thread_, NULL);
  }

  virtual void Run() noexcept {
    // Need to initialize the next_wakeup_time_ so it can be used to calculate
    // the first wakeup time after the program starts.
    clock_gettime(CLOCK_MONOTONIC, &next_wakeup_time_);

    while (true) {
      Loop();
      next_wakeup_time_ = AddTimespecByNs(next_wakeup_time_, period_ns_);
      clock_nanosleep(CLOCK_MONOTONIC, TIMER_ABSTIME, &next_wakeup_time_, NULL);
    }
  }

  virtual void Loop() noexcept {
    // RT loop iteration code here.
  }

 private:
  struct timespec AddTimespecByNs(struct timespec ts, int64_t ns) {
    ts.tv_nsec += ns;

    while (ts.tv_nsec >= 1'000'000'000) {
      ++ts.tv_sec;
      ts.tv_nsec -= 1'000'000'000;
    }

    while (ts.tv_nsec < 0) {
      --ts.tv_sec;
      ts.tv_nsec += 1'000'000'000;
    }

    return ts;
  }
};

void LockMemory() {
  int ret = mlockall(MCL_CURRENT | MCL_FUTURE);
  if (ret) {
    throw std::runtime_error{std::string("mlockall failed: ") + std::strerror(errno)};
  }
}

int main() {
  LockMemory();

  Thread rt_thread(80, SCHED_FIFO);
  rt_thread.Start();
  rt_thread.Join();

  return 0;
}
