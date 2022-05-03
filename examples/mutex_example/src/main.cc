#include <rt/rt.h>

#include <atomic>
#include <cmath>
#include <iomanip>
#include <iostream>
#include <thread>

#include "double_buffer.h"

using std::cout;

struct Data {
  double v1 = 0.0;
  double v2 = 0.0;
  double v3 = 0.0;
  double v4 = 0.0;
};

class RTThread : public rt::CyclicFifoThread {
  NaiveDoubleBuffer<Data>& buf_;

 public:
  RTThread(NaiveDoubleBuffer<Data>& buf)
      : CyclicFifoThread("RTThread", 1'000'000), buf_(buf) {
  }

 protected:
  bool Loop(int64_t ellapsed_ns) noexcept final {
    constexpr double period = 1000.0;
    constexpr double amplitude = 1.0;

    Data d;
    d.v1 = amplitude * cos(2 * M_PI / period * ellapsed_ns);
    d.v2 = d.v1 * 10;
    d.v3 = d.v1 * 100;
    d.v4 = d.v1 * 1000;

    buf_.Write(d);

    return false;
  }
};

class NonRTThread : public rt::Thread {
  NaiveDoubleBuffer<Data>& buf_;
  std::atomic_bool         should_stop_ = false;

 public:
  NonRTThread(NaiveDoubleBuffer<Data>& buf)
      : Thread("NonRTThread", 0, SCHED_OTHER), buf_(buf) {
  }

  void RequestStop() {
    should_stop_ = true;
  }

 protected:
  void Run() noexcept final {
    while (!should_stop_) {
      auto data = buf_.SwapAndRead();
      cout << "\33[2K\r" << std::flush;
      cout << std::showpos << std::setw(10) << data.v1 << " " << data.v2 << " " << data.v3 << " " << data.v4 << std::flush;

      std::this_thread::sleep_for(std::chrono::milliseconds(500));
    }
  }
};

class RTApp : public rt::App {
  NaiveDoubleBuffer<Data> buf_;
  RTThread                rt_thread_;
  NonRTThread             non_rt_thread_;

 public:
  RTApp() : App(0), rt_thread_(buf_), non_rt_thread_(buf_) {  // disable heap allocation
  }

  void Start() final {
    rt::App::Start();

    auto monotonic_now = rt::NowNs();
    auto wall_now = rt::WallNowNs();

    rt_thread_.Start(monotonic_now, wall_now);
    non_rt_thread_.Start(monotonic_now, wall_now);
  }

  void Join() {
    rt_thread_.Join();
    non_rt_thread_.Join();
  }

  void Stop() {
    rt_thread_.RequestStop();
    non_rt_thread_.RequestStop();
    Join();
  }
};

void TrivialDemo() {
  // Trivial demonstration that the double buffer does work..
  NaiveDoubleBuffer<int> buf;
  buf.Write(2);
  auto a = buf.SwapAndRead();
  cout << "a is " << a << std::endl;
}

int main() {
  TrivialDemo();

  RTApp app;
  app.Start();
  app.Join();

  return 0;
}
