#include <cactus_rt/rt.h>
#include <spdlog/spdlog.h>

#include <iceoryx_posh/internal/roudi/roudi.hpp>
#include <iceoryx_posh/roudi/iceoryx_roudi_components.hpp>
#include <iceoryx_posh/runtime/posh_runtime_single_process.hpp>

#include "publisher.h"
#include "subscriber.h"

class IceoryxExampleApp : public cactus_rt::App {
  std::unique_ptr<iox::roudi::IceOryxRouDiComponents>     iceoryx_roudi_components_;
  std::unique_ptr<iox::roudi::RouDi>                      iceoryx_roudi_;
  std::unique_ptr<iox::runtime::PoshRuntimeSingleProcess> iceoryx_runtime_;

  Publisher  publisher_;
  Subscriber subscriber_;

 public:
  IceoryxExampleApp() {
    // TODO: when iceoryx is included in the base framework, the thread
    // constructors can setup iceroyx publishers directly because the
    // constructor for cactus_rt::App would be the first thing that gets called
    // as it is the base class for this class. I.e. the SetupIceroyx can be
    // removed.
    SetupIceoryxRuntimeInSingleProcessMode();

    publisher_.SetupIceoryx();
    subscriber_.SetupIceoryx();

    RegisterThread(subscriber_);
    RegisterThread(publisher_);
  }

 private:
  void SetupIceoryxRuntimeInSingleProcessMode() {
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
};

int main() {
  spdlog::set_level(spdlog::level::debug);

  IceoryxExampleApp app;
  app.Start();
  app.Join();
  return 0;
}