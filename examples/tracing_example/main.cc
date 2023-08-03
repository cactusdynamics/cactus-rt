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

 public:
  ExampleRTThread(cactus_rt::CyclicThreadConfig config) : CyclicThread(config) {}

  int64_t GetLoopCounter() const {
    return loop_counter_;
  }

 protected:
  bool Loop(int64_t /*now*/) noexcept final {
    loop_counter_++;
    if (loop_counter_ % 1000 == 0) {
      LOG_INFO(Logger(), "Loop {}", loop_counter_);
    }

    Sense();
    Plan();
    Act();

    return false;
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

int main() {
  cactus_rt::CyclicThreadConfig thread_config;
  thread_config.name = "ExampleRTThread";
  thread_config.period_ns = 1'000'000;
  thread_config.cpu_affinity = std::vector<size_t>{2};
  thread_config.SetFifoScheduler(80);

  cactus_rt::AppConfig app_config;
  app_config.tracer_config.trace_aggregator_cpu_affinity = {1};

  auto thread = std::make_shared<ExampleRTThread>(thread_config);
  App  app(app_config);
  app.RegisterThread(thread);

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

  std::cout << "Number of loops executed: " << thread->GetLoopCounter() << "\n";
  return 0;
}
