#include <cactus_rt/rt.h>

#include <chrono>
#include <iostream>

#include "quill/LogMacros.h"   // Required for the logging macro
#include "quill/std/Chrono.h"  // Required to parse std::chrono inside logging macros

using cactus_rt::App;
using cactus_rt::CyclicThread;

/**
 * This is a thread that loops at 1 kHz. We always inherit from CyclicThread if
 * we want a thread that executes periodically.
 *
 * In this thread, we need to make sure we construct the cactus_rt::CyclicThread
 * object as a part of the constructor to initialize the thread. To write code
 * that executes at 1000 Hz, override and implement the Loop() function.
 *
 * This class demonstrates how it is done.
 */
class ExampleRTThread : public CyclicThread {
 public:
  /**
   * @brief Construct the thread. Note we are initializing the creating the
   * CyclicThread here with a predetermined name and config (via MakeConfig()).
   */
  ExampleRTThread() : CyclicThread("ExampleRTThread", MakeConfig()) {}

 protected:
  /**
   * @brief This methods runs every loop, which for this particular example is every 1ms.
   *
   * @param elapsed_ns The number of nanoseconds elapsed since the App::Start was called.
   * @return LoopControl::Continue if you want the thread to continue
   * @return LoopControl::Stop if you want to thread to stop
   */
  LoopControl Loop(int64_t elapsed_ns) noexcept final {
    // Code written in this function executes every 1 ms.

    // This demonstrates the usage of the quill logger. This emits a log message every 1s.
    LOG_INFO_LIMIT(std::chrono::seconds(1), Logger(), "Looping for {}", std::chrono::nanoseconds(elapsed_ns));

    // Return LoopControl::Stop if you want the thread to stop.
    return LoopControl::Continue;
  }

 private:
  /**
   * @brief Creates a CyclicThreadConfig object which configures this thread.
   */
  static cactus_rt::CyclicThreadConfig MakeConfig() {
    // This function sets up the thread configuration for this thread.
    cactus_rt::CyclicThreadConfig config;

    // Run at 1000 Hz.
    config.period_ns = 1'000'000;

    // Pin this thread on CPU core #2. If you don't want to pin in on a CPU core,
    // remove the following line.
    config.cpu_affinity = std::vector<size_t>{2};

    // Run the thread with SCHED_FIFO at real-time priority of 80.
    config.SetFifoScheduler(80);
    return config;
  }
};

int main() {
  // Sets up the signal handlers for SIGINT and SIGTERM (by default).
  cactus_rt::SetUpTerminationSignalHandler();

  // We first create cactus_rt App object.
  App app;

  // We then create a thread object. Threads should always be created via the
  // App::CreateThread factory method.
  auto thread = app.CreateThread<ExampleRTThread>();

  // Start the application, which starts all the registered threads (any thread
  // passed to App::RegisterThread) in the order they are registered.
  app.Start();

  std::cout << "App started\n";

  // This function blocks until SIGINT or SIGTERM are received.
  cactus_rt::WaitForAndHandleTerminationSignal();

  std::cout << "Caught signal, requesting stop...\n";

  // We ask the application to stop, which stops all threads in the order they
  // are created. If you want the application to run indefinitely, remove this
  // line.
  app.RequestStop();

  // We wait until all threads registered are done here.
  app.Join();

  std::cout << "Done\n";

  return 0;
}
