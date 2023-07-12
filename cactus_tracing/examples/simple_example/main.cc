#include <chrono>
#include <iostream>
#include <memory>

#include "cactus_tracing/thread_tracer.h"
#include "cactus_tracing/tracer.h"

using namespace std::chrono_literals;

int main() {
  auto& tracer = cactus_tracing::Tracer::Instance("My process", "data.perfetto-trace");

  std::shared_ptr<cactus_tracing::ThreadTracer> thread_tracer = std::make_shared<cactus_tracing::ThreadTracer>(
    "My thread",
    1919
  );

  tracer.RegisterThreadTracer(thread_tracer);

  {
    const auto span = thread_tracer->WithSpan("before start");
    std::this_thread::sleep_for(20ms);
  }

  tracer.StartBackgroundThread();

  {
    const auto span = thread_tracer->WithSpan("after start 1");
    std::this_thread::sleep_for(20ms);
  }

  {
    const auto span = thread_tracer->WithSpan("after start 2");
    std::this_thread::sleep_for(20ms);
  }

  tracer.StopBackgroundThread();
  tracer.JoinBackgroundThread();

  return 0;
}
