#include <cactus_rt/rt.h>

#include <chrono>
#include <iostream>

using cactus_rt::App;
using cactus_rt::CyclicThread;

// A custom function to waste some time so we generate good looking traces.
void WasteTime(std::chrono::nanoseconds duration) {
  const auto start = cactus_rt::NowNs();
  const auto duration_ns = duration.count();
  while (cactus_rt::NowNs() - start < duration_ns) {
  }
}

class ExampleRTThread : public CyclicThread {
  int64_t last_overrun_ = 0;  // A variable so we can generate an artificial loop overrun.

 public:
  ExampleRTThread() : CyclicThread("ExampleRTThread", CreateConfig()) {}

 protected:
  LoopControl Loop(int64_t elapsed_ns) noexcept final {
    // If this is a robot controller, we can imagine that the main loop function
    // will call three functions: sense, plan, and act. Each of these function
    // are traced with custom code in the function so we can see it in the trace.
    Sense();
    Plan();
    Act();

    // Cause an overrun every 1.5s to demonstrate the overrun detection and
    // marking feature. We simulate some rogue process that takes 1200us.
    if (elapsed_ns - last_overrun_ > 1'500'000'000) {
      last_overrun_ = elapsed_ns;
      auto span = Tracer().WithSpan("RogueSegment", "app");
      WasteTime(std::chrono::microseconds(1200));
    }

    return LoopControl::Continue;
  }

 private:
  void Sense() noexcept {
    // This uses RAII and emits a span with the duration that is the lifetime of
    // the span variable. In this case, the span variable lasts for the duration
    // of this function, which in this case we artificially constrain to 100us.
    //
    // The span has the name "Sense" and has the category of "app". All of these
    // can be queried from the Perfetto web UI.
    auto span = Tracer().WithSpan("Sense", "app");

    // Pretend that this code executes for 100us.
    WasteTime(std::chrono::microseconds(100));
  }

  void Plan() noexcept {
    // This uses RAII and emits a span with the duration that is the lifetime of
    // the span variable. In this case, the span variable lasts for the duration
    // of this function, which in this case we artificially constrain to 50us.
    //
    // The span has the name "Plan" and has the category of "app". All of these
    // can be queried from the Perfetto web UI.
    auto span = Tracer().WithSpan("Plan", "app");

    // Pretend that this code executes for 50us.
    WasteTime(std::chrono::microseconds(50));
  }

  void Act() noexcept {
    // This uses RAII and emits a span with the duration that is the lifetime of
    // the span variable. In this case, the span variable lasts for the duration
    // of this function, which in this case we artificially constrain to 75us.
    //
    // The span has the name "Act" and has the category of "app". All of these
    // can be queried from the Perfetto web UI.
    auto span = Tracer().WithSpan("Act", "app");

    // Pretend that this code executes for 75us.
    WasteTime(std::chrono::microseconds(75));
  }

  static cactus_rt::CyclicThreadConfig CreateConfig() {
    // This is a thread that runs every 1ms and is running with rtprio = 80.
    cactus_rt::CyclicThreadConfig thread_config;
    thread_config.period_ns = 1'000'000;
    thread_config.SetFifoScheduler(80);

    // cactus_rt will automatically trace the Loop latency as a span. It will
    // also automatically mark any Loop that overruns the configured period with
    // a marker. These can be turned off if not desired by uncommenting the
    // following lines:
    // thread_config.tracer_config.trace_loop = false;
    // thread_config.tracer_config.trace_overrun = false;

    // Uncomment this line if you want to see spans that indicates the sleeping
    // period of
    // thread_config.tracer_config.trace_sleep = true;

    // This enables the tracing of wakeup latency, which shows the latency
    // between when the thread is supposed to wake up and when the thread
    // actually wakes up.
    thread_config.tracer_config.trace_wakeup_latency = true;
    return thread_config;
  }
};

// Here we create a second real-time thread that runs at a lower frequency, to
// show that we can have multiple threads emitting trace data simultaneously.
class SecondRTThread : public CyclicThread {
 public:
  SecondRTThread() : CyclicThread("SecondRTThread", CreateThreadConfig()) {}

 protected:
  LoopControl Loop(int64_t /*now*/) noexcept final {
    WasteTime(std::chrono::microseconds(2000));
    return LoopControl::Continue;
  }

  static cactus_rt::CyclicThreadConfig CreateThreadConfig() {
    // This is a thread that runs every 3ms and is running with rtprio = 60.
    cactus_rt::CyclicThreadConfig thread_config;
    thread_config.period_ns = 3'000'000;
    thread_config.SetFifoScheduler(60);

    // thread_config.tracer_config.trace_sleep = true;
    thread_config.tracer_config.trace_wakeup_latency = true;
    return thread_config;
  }
};

int main() {
  cactus_rt::AppConfig app_config;
  // This should allow you to set where the background trace aggregator runs.
  // TODO: this feature is not yet implemented in the framework.
  app_config.tracer_config.trace_aggregator_cpu_affinity = {0};

  App app("TracingExampleApp", app_config);

  auto thread1 = app.CreateThread<ExampleRTThread>();
  auto thread2 = app.CreateThread<SecondRTThread>();

  std::cout << "Testing RT loop for 15 seconds with two trace sessions.\n";

  // Start the first trace session before the app starts so we capture all
  // events from the start of the app.
  app.StartTraceSession("build/data1.perfetto");

  app.Start();
  std::this_thread::sleep_for(std::chrono::seconds(5));

  // Stops the first session after 5 seconds. The app remains running but no
  // more trace data will be emitted.
  app.StopTraceSession();

  // Sleep another 5s without tracing data.
  std::this_thread::sleep_for(std::chrono::seconds(5));

  // Starts a second tracing session while the app is running and write the data
  // to a different location.
  app.StartTraceSession("build/data2.perfetto");
  std::this_thread::sleep_for(std::chrono::seconds(5));

  // Stops the app.
  app.RequestStop();
  app.Join();

  // Note we don't need to explicitly stop the trace session as the app
  // destructor will do it. If your app doesn't get destructed, you should
  // probably call StopTraceSession manually.
  return 0;
}
