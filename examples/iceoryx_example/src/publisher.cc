#include "publisher.h"

Publisher::Publisher() : cactus_rt::CyclicThread<cactus_rt::schedulers::Fifo>("Publisher", 1'000'000, cactus_rt::schedulers::Fifo::Config{80}) {
}

void Publisher::SetupIceoryx() {
  iox::popo::PublisherOptions publisherOptions;
  publisherOptions.historyCapacity = 10U;
  iceoryx_publisher_ = std::make_unique<iox::popo::Publisher<Data>>(
    iox::capro::ServiceDescription{"Single", "Process", "Demo"},  // TODO: need to rename the service
    publisherOptions);
}

bool Publisher::Loop(int64_t now) noexcept {
  auto start = cactus_rt::NowNs();
  // TODO: fully understand the future system.
  // TODO: is lambdas real-time safe?
  iceoryx_publisher_->loan().and_then([&](auto& sample) {
    sample->time = now;
    sample->last_publish_time_taken = last_publish_time_taken_;
    sample.publish();
  });

  auto end = cactus_rt::NowNs();
  last_publish_time_taken_ = end - start;
  return false;
}