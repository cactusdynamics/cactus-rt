#include <cactus_rt/rt.h>

#include <chrono>
#include <iostream>

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
   * @return true if you want the thread to stop
   * @return false if you want to thread to continue
   */
  LoopControl Loop(int64_t elapsed_ns) noexcept final {
    // Code written in this function executes every 1 ms.

    // This demonstrates the usage of the quill logger. This emits a log message every 1s.
    LOG_INFO_LIMIT(std::chrono::seconds(1), Logger(), "Looping for {}", std::chrono::nanoseconds(elapsed_ns));
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
  // We first create cactus_rt App object.
  App app;

  // We then create a thread object
  auto thread = std::make_shared<ExampleRTThread>();

  // We then register the thread with the app, which allows the app to start,
  // stop, and join the thread via App::Start, App::RequestStop, and App::Join.
  app.RegisterThread(thread);

  constexpr unsigned int time = 5;
  std::cout << "Testing RT loop for " << time << " seconds.\n";

  // Start the application, which starts all the registered threads (any thread
  // passed to App::RegisterThread) in the order they are registered.
  app.Start();

  // We let the application run for 5 seconds.
  std::this_thread::sleep_for(std::chrono::seconds(time));

  // We ask the application to stop, which stops all registered threads in the
  // order they are registered.
  app.RequestStop();

  // We wait until all threads registered are done here.
  app.Join();

  std::cout << "Done\n";

  return 0;
}
