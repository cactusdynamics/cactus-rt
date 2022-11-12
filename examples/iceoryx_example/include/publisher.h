#ifndef CACTUS_RT_EXAMPLES_ICEORYX_EXAMPLE_PUBLISHER_H_
#define CACTUS_RT_EXAMPLES_ICEORYX_EXAMPLE_PUBLISHER_H_

#include <cactus_rt/rt.h>

#include <iceoryx_posh/popo/publisher.hpp>
#include <memory>

#include "data.h"

class Publisher : public cactus_rt::CyclicFifoThread<> {
  int64_t                                     counter_ = 0;
  std::unique_ptr<iox::popo::Publisher<Data>> iceoryx_publisher_;

 public:
  Publisher();

 protected:
  bool Loop(int64_t now) noexcept final;
};

#endif