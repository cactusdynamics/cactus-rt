#include <cactus_rt/rt.h>
#include <spdlog/spdlog.h>

#include <iostream>

class CyclicThread : public cactus_rt::CyclicThread<cactus_rt::schedulers::Fifo> {
 public:
  CyclicThread()
      : cactus_rt::CyclicThread<cactus_rt::schedulers::Fifo>("CyclicThread", 1'000'000, /* Period */
                                                             cactus_rt::schedulers::Fifo::Config{80 /* Priority */}) {}

 protected:
  bool Loop(int64_t /*now*/) noexcept final {
    return false;
  }

  void AfterRun() final {
    SPDLOG_DEBUG("real-time thread exiting gracefully!");
    cactus_rt::CyclicThread<cactus_rt::schedulers::Fifo>::AfterRun();
  }
};

class RTApp : public cactus_rt::App {
  CyclicThread thread_;

 public:
  RTApp() {
    RegisterThread(thread_);
  }

  void Stop() {
    thread_.RequestStop();
    thread_.Join();
  }

  void OnTerminationSignal() final {
    Stop();
  }
};

int main() {
  spdlog::set_level(spdlog::level::debug);
  SPDLOG_DEBUG("signal handler example runs infinitely. press CTRL+C to interrupt and gracefully terminate");

  // Sets up the signal handlers for SIGINT and SIGTERM (by default).
  cactus_rt::SetupTerminationSignalHandler();

  // Create and start the application
  RTApp app;
  app.Start();

  // Wait until signals are caught, and then execute app.OnTerminationSignal(),
  // which in this cases causes the RT thread to gracefully exit.
  //
  // This function returns when app.OnTerminationSignal() finishes.
  cactus_rt::WaitUntilTerminationSignal(app);

  SPDLOG_DEBUG("main() exiting gracefully!");
  return 0;
}
