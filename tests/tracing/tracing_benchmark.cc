#include <benchmark/benchmark.h>
#include <cactus_rt/tracing/thread_tracer.h>
#include <cactus_rt/tracing/trace_aggregator.h>
#include <cactus_rt/tracing/tracing_enabled.h>

const uint32_t kQueueSize = 20'000'000;

// The for (auto _ : state) triggers the following rule...
// NOLINTBEGIN(clang-analyzer-deadcode.DeadStores)
namespace {
void BM_ThreadTracerWithSpanEnabledNoCategory(benchmark::State& state) {
  cactus_rt::tracing::EnableTracing();
  cactus_rt::tracing::ThreadTracer thread_tracer("benchmark_tracer", kQueueSize);
  for (auto _ : state) {
    thread_tracer.WithSpan("EventName");
  }
}
BENCHMARK(BM_ThreadTracerWithSpanEnabledNoCategory)->Iterations(kQueueSize / 2);

void BM_ThreadTracerWithSpanEnabledWithCategory(benchmark::State& state) {
  cactus_rt::tracing::EnableTracing();
  cactus_rt::tracing::ThreadTracer thread_tracer("benchmark_tracer", kQueueSize);
  for (auto _ : state) {
    thread_tracer.WithSpan("EventName", "category");
  }
}
BENCHMARK(BM_ThreadTracerWithSpanEnabledWithCategory)->Iterations(kQueueSize / 2);

void BM_ThreadTracerWithSpanDisabled(benchmark::State& state) {
  cactus_rt::tracing::DisableTracing();
  cactus_rt::tracing::ThreadTracer thread_tracer("benchmark_tracer", kQueueSize);
  for (auto _ : state) {
    thread_tracer.WithSpan("EventName", "category");
  }
}
BENCHMARK(BM_ThreadTracerWithSpanDisabled)->Iterations(kQueueSize / 2);

void BM_ThreadTracerWithSpanQueueFull(benchmark::State& state) {
  cactus_rt::tracing::EnableTracing();
  cactus_rt::tracing::ThreadTracer thread_tracer("benchmark_tracer", 2);
  for (auto _ : state) {
    thread_tracer.WithSpan("EventName", "category");
  }
}
BENCHMARK(BM_ThreadTracerWithSpanQueueFull)->Iterations(kQueueSize / 2);

void BM_TraceAgregatorThroughput(benchmark::State& state) {
  // In this test, we first queue up a large number of data into the queue and
  // then we measure how long it takes to empty the queue

  constexpr uint32_t queue_size = 1'000'000;

  cactus_rt::tracing::EnableTracing();

  using TraceAggregator = cactus_rt::tracing::TraceAggregator;
  using FileSink = cactus_rt::tracing::FileSink;
  using ThreadTracer = cactus_rt::tracing::ThreadTracer;

  // Setup trace aggregator and thread tracer without App
  TraceAggregator trace_aggregator{"benchmark_app"};

  auto file_sink = std::make_shared<FileSink>("data/benchmark.perfetto");
  trace_aggregator.RegisterSink(file_sink);

  auto thread_tracer = std::make_shared<ThreadTracer>("benchmark_tracer", queue_size);
  trace_aggregator.RegisterThreadTracer(thread_tracer);

  uint32_t x = 0;

  for (uint32_t i = 0; i < queue_size / 2; i++) {
    auto span = thread_tracer->WithSpan("TestData", "benchmark");
    benchmark::DoNotOptimize(x = 10);  // TODO: is this necessary
  }

  using Trace = cactus_tracing::vendor::perfetto::protos::Trace;

  for (auto _ : state) {
    while (true) {
      Trace trace;
      auto  events_written = trace_aggregator.DequeueSingleEventForEachTracer(trace);
      if (events_written > 0) {
        trace_aggregator.WriteTraceToAllSinks(trace);
      } else {
        break;
      }
    }
  }
}
BENCHMARK(BM_TraceAgregatorThroughput)->Iterations(10);

}  // namespace

BENCHMARK_MAIN();

// NOLINTEND(clang-analyzer-deadcode.DeadStores)
