#include <cactus_rt/rt.h>
#include <simpleudp.h>
#include <spdlog/spdlog.h>

#include <array>
#include <iostream>
#include <stdexcept>

#include "robot_instantaneous_data_generated.h"

using cactus_rt::simpleudp::Error;
using cactus_rt::simpleudp::SimpleUDP;
// using cactus_rt::examples::udp_example

constexpr const char* kData = "123456789 123456789 123456789 123456789 123456789 123456789 12345678 123456789 123456789 123456789";
constexpr size_t      kDataSize = strlen(kData);

constexpr int kMaxConsecutiveErrors = 5;

// A no-op thread that only serves to do nothing and measure the latency
class CyclicRTSendThread : public cactus_rt::CyclicThread<cactus_rt::schedulers::Fifo> {
  SimpleUDP client_;

  size_t                                   consecutive_error_count_ = 0;
  size_t                                   cumulative_error_count_ = 0;
  std::array<Error, kMaxConsecutiveErrors> errors_;

 public:
  CyclicRTSendThread(const char* ip, const char* port)
      : cactus_rt::CyclicThread<cactus_rt::schedulers::Fifo>("CyclicRTSendThread", 1'000'000, /* Period */
                                                             cactus_rt::schedulers::Fifo::Config{70 /* Priority */}),
        client_(ip, port) {}

 protected:
  void BeforeRun() final {
    auto err = client_.Connect();
    if (err) {
      throw std::runtime_error{err->ToString()};
    }
  };

  bool Loop(int64_t now) noexcept final {
    auto [_bytes_sent, err] = client_.Send(kData, kDataSize);
    if (err) {
      // We tolerate up to kMaxConsecutiveErrors.
      // We store all the errors seen in the errors_ array which can be fetched later.
      errors_[consecutive_error_count_] = err.value();
      consecutive_error_count_++;
      cumulative_error_count_++;
      if (consecutive_error_count_ >= kMaxConsecutiveErrors) {
        return true;
      }
    } else {
      // TODO: log that the errors are reset.
      // If we succeed again, we reset this.
      // Note: since this is the client and UDP can be lossy, not returning an
      // error doesn't necessarily mean the messages are sent properly..
      consecutive_error_count_ = 0;
      // Don't need to wipe errors_ because we will just overwrite it anyway.
    }

    return false;
  }

  void AfterRun() final {
    if (consecutive_error_count_ > 0) {
      SPDLOG_ERROR("failed to send {} times with errors:", consecutive_error_count_);
      for (size_t i = 0; i < consecutive_error_count_; i++) {
        SPDLOG_ERROR(" - {}", errors_.at(i).ToString());
      }
    }

    if (cumulative_error_count_ > 0) {
      SPDLOG_WARN("failed to send {} times total", cumulative_error_count_);
    }
  }
};

class ClientRTApp : public cactus_rt::App {
  CyclicRTSendThread send_thread_;

 public:
  ClientRTApp(const char* ip, const char* port) : send_thread_(ip, port) {
    RegisterThread(send_thread_);
  }
};

int main(int argc, char* argv[]) {
  const char* ip = "127.0.0.1";
  if (argc > 1) {
    ip = argv[1];
  }

  spdlog::set_level(spdlog::level::debug);
  SPDLOG_DEBUG("connecting to {}", ip);
  ClientRTApp app(ip, "7838");

  app.Start();
  app.Join();

  return 0;
}
