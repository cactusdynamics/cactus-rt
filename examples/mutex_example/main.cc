#include <cactus_rt/rt.h>

#include <chrono>
#include <cmath>
#include <iostream>

#include "double_buffer.h"

using cactus_rt::App;
using cactus_rt::CyclicThread;
using cactus_rt::Thread;

struct Data {
  double v1 = 0.0;
  double v2 = 0.0;
  double v3 = 0.0;
  double v4 = 0.0;
};

class RTThread : public CyclicThread {
  NaiveDoubleBuffer<Data>& buf_;

 public:
  explicit RTThread(const char* name, cactus_rt::CyclicThreadConfig config, NaiveDoubleBuffer<Data>& buf)
      : CyclicThread(name, config),
        buf_(buf) {}

 protected:
  LoopControl Loop(int64_t ellapsed_ns) noexcept final {
    constexpr double period = 5'000'000'000.0;  // 5 seconds period
    constexpr double amplitude = 1.0;

    Data d;
    d.v1 = static_cast<double>(ellapsed_ns) / 1'000'000'000.0;
    d.v2 = static_cast<double>(ellapsed_ns) / 1'000'000.0;
    d.v3 = amplitude * cos(2 * M_PI / period * static_cast<double>(ellapsed_ns));
    d.v4 = d.v3 * 10;

    buf_.Write(d);

    return LoopControl::Continue;
  }
};

class NonRTThread : public Thread {
  NaiveDoubleBuffer<Data>& buf_;

 public:
  explicit NonRTThread(const char* name, cactus_rt::CyclicThreadConfig config, NaiveDoubleBuffer<Data>& buf)
      : Thread(name, config), buf_(buf) {}

 protected:
  void Run() final {
    while (!this->StopRequested()) {
      auto data = buf_.SwapAndRead();
      LOG_INFO(Logger(), "time_ns={}; time_us={}; f(t) = {}; 10*f(t) = {}", data.v1, data.v2, data.v3, data.v4);

      std::this_thread::sleep_for(std::chrono::milliseconds(500));
    }
  }
};

void TrivialDemo() {
  // Trivial demonstration that the double buffer does work..
  NaiveDoubleBuffer<int> buf;
  buf.Write(2);
  auto a = buf.SwapAndRead();
  std::cout << "a is " << a << std::endl;
}

void ThreadedDemo() {
  cactus_rt::CyclicThreadConfig rt_thread_config;
  rt_thread_config.period_ns = 1'000'000;
  rt_thread_config.SetFifoScheduler(80 /* priority */);

  cactus_rt::CyclicThreadConfig non_rt_thread_config;
  non_rt_thread_config.SetOtherScheduler(0 /* niceness */);

  // The double buffer is shared between the two threads, so we pass a reference
  // into the thread and maintain the object lifetime to this function.
  NaiveDoubleBuffer<Data> buf;

  App app;

  auto rt_thread = app.CreateThread<RTThread>("RTThread", rt_thread_config, buf);
  auto non_rt_thread = app.CreateThread<NonRTThread>("NonRTThread", non_rt_thread_config, buf);

  constexpr unsigned int time = 10;
  app.Start();
  std::this_thread::sleep_for(std::chrono::seconds(time));
  app.RequestStop();
  app.Join();
}

int main() {
  TrivialDemo();
  ThreadedDemo();
  return 0;
}
