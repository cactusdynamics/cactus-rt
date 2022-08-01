#include <cactus_rt/rt.h>
#include <spdlog/spdlog.h>

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

class RTThread : public cactus_rt::CyclicFifoThread<> {
  NaiveDoubleBuffer<Data>& buf_;

 public:
  RTThread(NaiveDoubleBuffer<Data>& buf)
      : CyclicFifoThread<>("RTThread", 1'000'000), buf_(buf) {
  }

 protected:
  // NOLINTBEGIN(bugprone-exception-escape)
  // TODO: The BasicLockable definition requires the lock() method to throw upon error.
  // RT code shouldn't use exceptions.
  //
  // Not sure what the best course of action here is. One thing we can do is
  // create a cactus_rt::scoped_lock that mimics the std::scoped_lock
  // interface, but only works with cactus_rt::mutex.
  bool Loop(int64_t ellapsed_ns) noexcept final {
    constexpr double period = 5'000'000'000.0;  // 5 seconds period
    constexpr double amplitude = 1.0;

    Data d;
    d.v1 = ellapsed_ns / 1'000'000'000.0;
    d.v2 = ellapsed_ns / 1'000'000.0;
    d.v3 = amplitude * cos(2 * M_PI / period * ellapsed_ns);
    d.v4 = d.v3 * 10;

    buf_.Write(d);

    return false;
  }
  // NOLINTEND(bugprone-exception-escape)
};

class NonRTThread : public cactus_rt::Thread {
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
  void Run() final {
    while (!should_stop_) {
      auto data = buf_.SwapAndRead();
      cout << "\33[2K\r" << std::flush;
      cout << std::showpos << std::setw(10) << data.v1 << " " << data.v2 << " " << data.v3 << " " << data.v4 << std::flush;

      std::this_thread::sleep_for(std::chrono::milliseconds(500));
    }
  }
};

class RTApp : public cactus_rt::App {
  NaiveDoubleBuffer<Data> buf_;
  RTThread                rt_thread_;
  NonRTThread             non_rt_thread_;

 public:
  RTApp() : App(0), rt_thread_(buf_), non_rt_thread_(buf_) {  // disable heap allocation
  }

  void Start() final {
    cactus_rt::App::Start();

    auto monotonic_now = cactus_rt::NowNs();
    auto wall_now = cactus_rt::WallNowNs();

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

// NOLINTBEGIN(bugprone-exception-escape)
void TrivialDemo() {
  // Trivial demonstration that the double buffer does work..
  NaiveDoubleBuffer<int> buf;
  buf.Write(2);
  auto a = buf.SwapAndRead();
  cout << "a is " << a << std::endl;
}

int main() {
  spdlog::set_level(spdlog::level::debug);
  TrivialDemo();

  RTApp app;
  app.Start();
  app.Join();

  return 0;
}
// NOLINTEND(bugprone-exception-escape)