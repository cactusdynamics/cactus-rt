#ifndef CACTUS_RT_EXAMPLES_ICEORYX_EXAMPLE_APP_H_
#define CACTUS_RT_EXAMPLES_ICEORYX_EXAMPLE_APP_H_

#include <cactus_rt/rt.h>

#include <iceoryx_posh/internal/roudi/roudi.hpp>
#include <iceoryx_posh/roudi/iceoryx_roudi_components.hpp>
#include <iceoryx_posh/runtime/posh_runtime_single_process.hpp>
#include <memory>

class App : public cactus_rt::App {
  std::unique_ptr<iox::roudi::IceOryxRouDiComponents>     iceoryx_roudi_components_;
  std::unique_ptr<iox::roudi::RouDi>                      iceoryx_roudi_;
  std::unique_ptr<iox::runtime::PoshRuntimeSingleProcess> iceoryx_runtime_;

  std::vector<std::unique_ptr<cactus_rt::Thread>> threads_;

 public:
  App();

  // TODO: refactor some of this into the base App class.
  // TODO: the base thread should have a request stop?
  void RegisterThread(std::unique_ptr<cactus_rt::Thread> thread);
  void Start() override;
  void Join();

 private:
  void SetupSingleProcessIceoryxRuntime();
};

#endif