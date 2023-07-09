#include <cactus_rt/rt.h>

#include <cmath>

#include "double_buffer.h"

using cactus_rt::App;
using cactus_rt::CyclicThread;
using cactus_rt::Thread;
using cactus_rt::schedulers::Fifo;
using cactus_rt::schedulers::Other;

struct Data {
  double v1 = 0.0;
  double v2 = 0.0;
  double v3 = 0.0;
  double v4 = 0.0;
};

class RTThread : public CyclicThread<> {
  NaiveDoubleBuffer<Data>& buf_;

 public:
  explicit RTThread(NaiveDoubleBuffer<Data>& buf) : CyclicThread<>(
                                                      "RTThread",
                                                      1'000'000,  // Period in ns
                                                      Fifo::Config{80 /* Priority */}
                                                    ),
                                                    buf_(buf) {}

 protected:
  bool Loop(int64_t ellapsed_ns) noexcept final {
    constexpr double period = 5'000'000'000.0;  // 5 seconds period
    constexpr double amplitude = 1.0;

    Data d;
    d.v1 = static_cast<double>(ellapsed_ns) / 1'000'000'000.0;
    d.v2 = static_cast<double>(ellapsed_ns) / 1'000'000.0;
    d.v3 = amplitude * cos(2 * M_PI / period * static_cast<double>(ellapsed_ns));
    d.v4 = d.v3 * 10;

    buf_.Write(d);

    return false;
  }
};

class NonRTThread : public Thread<Other> {
  NaiveDoubleBuffer<Data>& buf_;

 public:
  explicit NonRTThread(NaiveDoubleBuffer<Data>& buf) : Thread<Other>("NonRTThread"), buf_(buf) {}

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
  // The double buffer is shared between the two threads, so we pass a reference
  // into the thread and maintain the object lifetime to this function.
  NaiveDoubleBuffer<Data> buf;

  auto rt_thread = std::make_shared<RTThread>(buf);
  auto non_rt_thread = std::make_shared<NonRTThread>(buf);
  App  app;

  app.RegisterThread(non_rt_thread);
  app.RegisterThread(rt_thread);

  constexpr unsigned int time = 10;
  app.Start();
  sleep(time);
  app.RequestStop();
  app.Join();
}

int main() {
  TrivialDemo();
  ThreadedDemo();
  return 0;
}
