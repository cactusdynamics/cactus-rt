#include <cactus_rt/rt.h>
#include <semaphore.h>
#include <spdlog/spdlog.h>

#include <csignal>
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

  inline static sem_t signal_semaphore_;

  RTApp() {
    RegisterThread(thread_);
  }

  static void SetupTerminationSignalHandling() {
    int ret = sem_init(&signal_semaphore_, 0, 0);
    if (ret != 0) {
      throw std::runtime_error{std::string("cannot initialize semaphore: ") + std::strerror(errno)};
    }

    auto sig_ret = std::signal(SIGINT, SignalHandler);
    if (sig_ret == SIG_ERR) {
      throw std::runtime_error("failed to register signal handler");
    }

    sig_ret = std::signal(SIGTERM, SignalHandler);
    if (sig_ret == SIG_ERR) {
      throw std::runtime_error("failed to register signal handler");
    }
  }

  static void SignalHandler(int /*sig*/) {
    // From the man page (sem_post(3)), it says:
    //
    // > sem_post() is async-signal-safe: it may be safely called within a
    // > signal handler.
    //
    // This allows it to be used for signaling for an async signal handler. This
    // is also according to Programming with POSIX Threads by Butenhof in 1997,
    // section 6.6.6.
    //
    // However, the situation is more complex, see https://stackoverflow.com/questions/48584862/sem-post-signal-handlers-and-undefined-behavior.
    // That said, overall this should be a good pattern to use.
    write(STDERR_FILENO, "synchronous signal handler active\n", 34);
    int ret = sem_post(&signal_semaphore_);
    if (ret != 0) {
      write(STDERR_FILENO, "failed to post semaphore\n", 25);
      std::_Exit(EXIT_FAILURE);
    }
  }

 public:
  static RTApp& Instance() {
    static RTApp app;
    return app;
  }

  void Start() override {
    cactus_rt::App::Start();
    SetupTerminationSignalHandling();
  }

  void Stop() {
    thread_.RequestStop();
    thread_.Join();
  }

  void WaitForTerminationSignal() {
    while (sem_wait(&signal_semaphore_) == -1) {
      SPDLOG_DEBUG("waiting on semaphore...");
    }

    SPDLOG_INFO("async signal handler active, stopping real-time threads");
    Stop();
    // TODO: call a custom function that the user can override once merged back to cactus_rt::App.
  }
};

int main() {
  spdlog::set_level(spdlog::level::debug);

  SPDLOG_DEBUG("signal handler example runs infinitely. press CTRL+C to interrupt and gracefully terminate");
  RTApp& app = RTApp::Instance();
  app.Start();
  app.WaitForTerminationSignal();

  return 0;
}
