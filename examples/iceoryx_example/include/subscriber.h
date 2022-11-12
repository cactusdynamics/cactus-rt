#ifndef CACTUS_RT_EXAMPLES_ICEORYX_EXAMPLE_SUBSCRIBER_H_
#define CACTUS_RT_EXAMPLES_ICEORYX_EXAMPLE_SUBSCRIBER_H_

#include <cactus_rt/rt.h>

#include <fstream>
#include <iceoryx_posh/popo/subscriber.hpp>
#include <memory>
#include <vector>

#include "data.h"

class Subscriber : public cactus_rt::Thread {
  std::unique_ptr<iox::popo::Subscriber<Data>> iceoryx_subscriber_;
  std::vector<Data>                            data_buffer_;

  std::ofstream data_file_;

 public:
  Subscriber();
  void Run() final;
};

#endif
