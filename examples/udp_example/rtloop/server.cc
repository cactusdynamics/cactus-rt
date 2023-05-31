#include <cactus_rt/rt.h>
#include <simpleudp.h>
#include <spdlog/spdlog.h>

#include <array>
#include <iostream>
#include <stdexcept>

using cactus_rt::simpleudp::Error;
using cactus_rt::simpleudp::SimpleUDP;

constexpr int kBufSize = 1024;
constexpr int kMaxConsecutiveErrors = 5;

// A no-op thread that only serves to do nothing and measure the latency
class CyclicRTRecvThread : public cactus_rt::CyclicThread<cactus_rt::schedulers::Fifo> {
  SimpleUDP client_;

  size_t                                   consecutive_error_count_ = 0;
  size_t                                   cumulative_error_count_ = 0;
  std::array<Error, kMaxConsecutiveErrors> errors_;

  char   buf_[kBufSize] = {0};
  size_t messages_received_ = 0;
  size_t bytes_received_ = 0;

 public:
  CyclicRTRecvThread(const char* ip, const char* port)
      : cactus_rt::CyclicThread<cactus_rt::schedulers::Fifo>("CyclicRTRecvThread", 1'000'000, /* Period */
                                                             cactus_rt::schedulers::Fifo::Config{70 /* Priority */}),
        client_(ip, port) {}

 protected:
  void BeforeRun() final {
    auto err = client_.Bind();
    if (err) {
      throw std::runtime_error{err->ToString()};
    }
  };

  bool Loop(int64_t now) noexcept final {
    auto [bytes_received, err] = client_.Recv(buf_, kBufSize - 1);
    if (err) {
      if (err->IsEAgain()) {
        return false;  // This means there's nothing to receive. Is that an error?? Not initially so we need a state machine to establish connection. Yay we are reimplementing TCP.
      }

      // We tolerate up to kMaxConsecutiveErrors.
      // We store all the errors seen in the errors_ array which can be fetched later.
      errors_[consecutive_error_count_] = err.value();
      consecutive_error_count_++;
      cumulative_error_count_++;
      if (consecutive_error_count_ >= kMaxConsecutiveErrors) {
        return true;
      }

      return false;
    } else {
      // TOOD: log that the errors are reset.
      // If we succeed again, we reset this.
      // Note: since UDP is lossing, not returning an error doesn't necessarily
      // mean the messages are sent properly..
      consecutive_error_count_ = 0;
      // Don't need to wipe errors_ because we will just overwrite it anyway.

      messages_received_++;
      bytes_received_ += bytes_received;
      buf_[bytes_received] = '\0';

      if (bytes_received_ > 5000 * 100) {
        return true;  // This is about 5 seconds of data in this demo... The server quits so we can print some stats.
      }
    }

    return false;
  }

  void AfterRun() final {
    if (consecutive_error_count_ > 0) {
      SPDLOG_ERROR("failed to recv {} times with errors:", consecutive_error_count_);
      for (size_t i = 0; i < consecutive_error_count_; i++) {
        SPDLOG_ERROR(" - {}", errors_.at(i).ToString());
      }
    }

    if (cumulative_error_count_ > 0) {
      SPDLOG_WARN("failed to recv {} times total", cumulative_error_count_);
    }

    SPDLOG_INFO("received {} messages and {} bytes", messages_received_, bytes_received_);

    SPDLOG_INFO("Last message: {}", buf_);

    CyclicThread::AfterRun();
  }
};

class ClientRTApp : public cactus_rt::App {
  CyclicRTRecvThread send_thread_;

 public:
  ClientRTApp(const char* ip, const char* port) : send_thread_(ip, port) {
    RegisterThread(send_thread_);
  }
};

int main() {
  spdlog::set_level(spdlog::level::debug);
  ClientRTApp app("0.0.0.0", "7838");

  app.Start();
  app.Join();

  return 0;
}
