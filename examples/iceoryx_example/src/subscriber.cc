#include "subscriber.h"

#include <spdlog/spdlog.h>

Subscriber::Subscriber() : cactus_rt::Thread<cactus_rt::schedulers::Other>("Subscriber") {
}

void Subscriber::SetupIceoryx() {
  iox::popo::SubscriberOptions options;
  options.queueCapacity = 10U;
  options.historyRequest = 5U;
  iceoryx_subscriber_ = std::make_unique<iox::popo::Subscriber<Data>>(
    iox::capro::ServiceDescription{"Single", "Process", "Demo"},
    options);

  data_buffer_.reserve(8000);  // big enough...

  data_file_.open("data.csv");
  if (!data_file_.is_open()) {
    throw std::runtime_error{"failed to open data file"};
  }
}

void Subscriber::Run() {
  while (!this->StopRequested()) {
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
      size_t n = 0;
      for (const auto& data : data_buffer_) {
        data_file_ << data.time << ", " << data.last_publish_time_taken << "\n";
        ++n;
      }

      SPDLOG_DEBUG("wrote {} entries to file", n);

      // don't think this is fast. Ideally we just start the buffer from beginning without necessarily zeroing out the data.
      data_buffer_.clear();
    }
  }
}