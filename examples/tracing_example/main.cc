#include <cactus_rt/rt.h>

#include <chrono>
#include <iostream>

using cactus_rt::App;
using cactus_rt::CyclicThread;

void WasteTime(std::chrono::microseconds duration) {
  const auto start = cactus_rt::NowNs();
  auto       duration_ns = duration.count() * 1000;
  while (cactus_rt::NowNs() - start < duration_ns) {
  }
}

class ExampleRTThread : public CyclicThread {
  int64_t loop_counter_ = 0;

  static cactus_rt::CyclicThreadConfig CreateThreadConfig() {
    cactus_rt::CyclicThreadConfig thread_config;
    thread_config.period_ns = 1'000'000;
    thread_config.cpu_affinity = std::vector<size_t>{2};
    thread_config.SetFifoScheduler(80);

    // thread_config.tracer_config.trace_sleep = true;
    thread_config.tracer_config.trace_wakeup_latency = true;
    return thread_config;
  }

 public:
  ExampleRTThread() : CyclicThread("ExampleRTThread", CreateThreadConfig()) {}

  int64_t GetLoopCounter() const {
    return loop_counter_;
  }

 protected:
  LoopControl Loop(int64_t /*now*/) noexcept final {
    loop_counter_++;
    if (loop_counter_ % 1000 == 0) {
      LOG_INFO(Logger(), "Loop {}", loop_counter_);
    }

    Sense();
    Plan();
    Act();

    // Cause an overrun every 1.5s to demonstrate the overrun detection and marking feature.
    if (loop_counter_ % 1500 == 0) {
      auto span = Tracer().WithSpan("RogueSegment", "app");
      WasteTime(std::chrono::microseconds(1200));
    }

    return LoopControl::Continue;
  }

 private:
  void Sense() noexcept {
    auto span = Tracer().WithSpan("Sense", "app");
    WasteTime(std::chrono::microseconds(100));
  }

  void Plan() noexcept {
    auto span = Tracer().WithSpan("Plan", "app");
    WasteTime(std::chrono::microseconds(50));
  }

  void Act() noexcept {
    auto span = Tracer().WithSpan("Act", "app");
    WasteTime(std::chrono::microseconds(75));
  }
};

class SecondRTThread : public CyclicThread {
  static cactus_rt::CyclicThreadConfig CreateThreadConfig() {
    cactus_rt::CyclicThreadConfig thread_config;
    thread_config.period_ns = 3'000'000;
    thread_config.cpu_affinity = {1};
    thread_config.SetFifoScheduler(60);

    // thread_config.tracer_config.trace_sleep = true;
    thread_config.tracer_config.trace_wakeup_latency = true;
    return thread_config;
  }

 public:
  SecondRTThread() : CyclicThread("SecondRTThread", CreateThreadConfig()) {}

 protected:
  LoopControl Loop(int64_t /*now*/) noexcept final {
    const auto span = Tracer().WithSpan("Sense");
    WasteTime(std::chrono::microseconds(2000));
    return LoopControl::Continue;
  }
};

int main() {
  cactus_rt::AppConfig app_config;
  app_config.tracer_config.trace_aggregator_cpu_affinity = {0};  // doesn't work yet

  auto thread1 = std::make_shared<ExampleRTThread>();
  auto thread2 = std::make_shared<SecondRTThread>();
  App  app("TracingExampleApp", app_config);
  app.RegisterThread(thread1);
  app.RegisterThread(thread2);

  std::cout << "Testing RT loop for 15 seconds with two trace sessions.\n";

  // Start the first trace session before the app starts so we capture all
  // events from the start.
  app.StartTraceSession("build/data1.perfetto");
  app.Start();
  std::this_thread::sleep_for(std::chrono::seconds(5));
  // Stops the first session after 5 seconds.
  app.StopTraceSession();

  std::this_thread::sleep_for(std::chrono::seconds(5));

  // Starts a second session after 5 seconds.
  app.StartTraceSession("build/data2.perfetto");
  std::this_thread::sleep_for(std::chrono::seconds(5));

  // Stops the app.
  app.RequestStop();
  app.Join();
  // Don't need to stop the trace session as the app destructor will take care of it.

  std::cout << "Number of loops executed: " << thread1->GetLoopCounter() << "\n";
  return 0;
}
