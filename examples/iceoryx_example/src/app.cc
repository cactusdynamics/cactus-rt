#include "app.h"

App::App() {
  SetupSingleProcessIceoryxRuntime();
}

void App::RegisterThread(std::unique_ptr<cactus_rt::Thread> thread) {
  threads_.push_back(std::move(thread));
}

void App::Start() {
  cactus_rt::App::Start();

  for (auto& thread : threads_) {
    thread->Start(start_monotonic_time_ns_, start_wall_time_ns_);
  }
}

void App::Join() {
  for (auto& thread : threads_) {
    thread->Join();
  }
}

void App::SetupSingleProcessIceoryxRuntime() {
  iox::RouDiConfig_t default_config = iox::RouDiConfig_t().setDefaults();
  iceoryx_roudi_components_ = std::make_unique<iox::roudi::IceOryxRouDiComponents>(default_config);

  // The last bool parameter in RoudiStartupParameters states that RouDi does
  // not terminate all registered processes when RouDi goes out of scope. If
  // we would set it to true, our application would self terminate in the
  // destructor of roudi
  //
  // TODO: understand what monitoring mode is
  // TODO: what is the difference between IceoryxRoudiComponents and Roudi?
  iceoryx_roudi_ = std::make_unique<iox::roudi::RouDi>(
    iceoryx_roudi_components_->rouDiMemoryManager,
    iceoryx_roudi_components_->portManager,
    iox::roudi::RouDi::RoudiStartupParameters{iox::roudi::MonitoringMode::OFF, false});

  iceoryx_runtime_ = std::make_unique<iox::runtime::PoshRuntimeSingleProcess>("rt_iceoryx_example");
}