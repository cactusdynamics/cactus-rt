#include <cactus_rt/tracing.h>

#include <list>
#include <memory>
#include <thread>

using namespace std::chrono_literals;
using FileSink = cactus_rt::tracing::FileSink;
using TraceAggregator = cactus_rt::tracing::TraceAggregator;
using ThreadTracer = cactus_rt::tracing::ThreadTracer;

// We should have only at most one TraceAggregator per process. We use a pointer
// as we don't want to enable tracing all the time and would like to disable
// tracing sometimes to save CPU overhead and disk space.
std::unique_ptr<TraceAggregator> trace_aggregator = nullptr;

// This can be called multiple times. However, it must be called after
// StopTracing() has been called once. It is not thread safe.
void StartTracing(const char* app_name, const char* filename) {
  // Enable the tracing.
  cactus_rt::tracing::EnableTracing();

  // Create the trace aggregator that will pop the queues and write the events to sinks.
  trace_aggregator = std::make_unique<TraceAggregator>(app_name);

  // Create the file sink so the data aggregated by the TraceAggregator will be written to somewhere.
  auto file_sink = std::make_shared<FileSink>(filename);
  trace_aggregator->RegisterSink(file_sink);

  trace_aggregator->Start();
}

void StopTracing() {
  cactus_rt::tracing::DisableTracing();

  trace_aggregator->RequestStop();
  trace_aggregator->Join();
  trace_aggregator = nullptr;  // Destroy the trace aggregator and free all resources.
}

int main() {
  auto main_thread_tracer = std::make_shared<ThreadTracer>("main_thread");
  auto thread1_tracer = std::make_shared<ThreadTracer>("thread1");

  StartTracing("tracing_example_no_cactus_rt", "build/no-rt.perfetto");

  std::thread t([thread1_tracer]() {
    for (int i = 0; i < 10; i++) {
      {
        auto span = thread1_tracer->WithSpan("thread1span");
        std::this_thread::sleep_for(100ms);
      }
      std::this_thread::sleep_for(50ms);
    }
  });

  for (int i = 0; i < 5; i++) {
    {
      auto span = main_thread_tracer->WithSpan("mainspan");
      std::this_thread::sleep_for(150ms);
    }
    std::this_thread::sleep_for(25ms);
  }

  t.join();
  StopTracing();
  return 0;
}
