#include "subscriber.h"

Subscriber::Subscriber() : cactus_rt::Thread("Subscriber", 0) {
  iox::popo::SubscriberOptions options;
  options.queueCapacity = 10U;
  options.historyRequest = 5U;
  iceoryx_subscriber_ = std::make_unique<iox::popo::Subscriber<Data>>(
    iox::capro::ServiceDescription{"Single", "Process", "Demo"},
    options);

  data_buffer_.reserve(8000);  // big enough...
}

void Subscriber::Run() {
  while (true) {
    if (iceoryx_subscriber_->getSubscriptionState() != iox::SubscribeState::SUBSCRIBED) {
      // TODO: busy way is probably not that great?
      continue;
    }

    bool has_more_samples = true;
    while (has_more_samples) {
      iceoryx_subscriber_->take()
        .and_then([&](auto& sample) {
          data_buffer_.emplace_back(*sample);
        })
        .or_else([&](auto& result) {
          has_more_samples = false;
          if (result != iox::popo::ChunkReceiveResult::NO_CHUNK_AVAILABLE) {
            // Errors other than an empty queue! Needs handling
            // TOOD: figure out what to do when no chunks are available
          }
        });
    }

    if (data_buffer_.size() >= 1000) {
      for (const auto& data : data_buffer_) {
        std::cout << data.t << ", " << data.counter << "\n";
      }

      // don't think this is fast. Ideally we just start the buffer from beginning without necessarily zeroing out the data.
      data_buffer_.clear();
    }
  }
}