#include <benchmark/benchmark.h>
#include <cactus_rt/tracing/thread_tracer.h>
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
}  // namespace

BENCHMARK_MAIN();

// NOLINTEND(clang-analyzer-deadcode.DeadStores)
