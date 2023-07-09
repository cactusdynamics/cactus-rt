#ifndef CACTUS_RT_EXAMPLES_MESSAGE_PASSING_EXAMPLE_DATA_LOGGER_H_
#define CACTUS_RT_EXAMPLES_MESSAGE_PASSING_EXAMPLE_DATA_LOGGER_H_

#include <cactus_rt/rt.h>
#include <readerwriterqueue.h>

#include <atomic>
#include <cstdint>
#include <fstream>
#include <tuple>
#include <vector>

using moodycamel::ReaderWriterQueue;

using cactus_rt::Thread;
using cactus_rt::schedulers::Other;

struct OutputData {
  double timestamp = 0;
  double output_value = 0.0;

  OutputData() = default;
  OutputData(double t, double o) : timestamp(t), output_value(o) {}
};

class DataLogger : public Thread<Other> {
  constexpr static int kQueueCapacity = 8 * 1024;  // This is over 8 seconds of data while we write every 1 second. Should never be full.

  int64_t period_ns_;
  int64_t write_data_interval_ns_;

  ReaderWriterQueue<OutputData> queue_;

  // Want to ensure that the message count is always updated in a single
  // operation? Maybe this is not necessary tho, but this is still a cool
  // technique to pass data around if you can fit in a word.
  // Also see: https://stackoverflow.com/questions/56275443/why-is-it-not-possible-to-instantiate-an-atomic-pair
  using CountData = struct {
    uint32_t successful_messages;
    uint32_t total_messages;
  };

  using AtomicMessageCount = std::atomic<CountData>;
  AtomicMessageCount message_count_;
  static_assert(AtomicMessageCount::is_always_lock_free);

  std::vector<OutputData> data_buffer_;  // A simple buffer to hold the data in non-realtime thread so batch writing can occur

  std::ofstream file_;

 public:
  /**
   * Creates a new data logger thread.
   *
   * @param data_file_path The path to the CSV file to be saved.
   * @param period_ns The period in us at which the data logger thread will run
   *                  at. Default: 10ms. No good reason for this
   *                  value other than a guess that it might reduce scheduler
   *                  load? Probably not as this thread is a normal thread.
   * @param write_data_interval_ns The interval in seconds at which the
   *                               data is written to the CSV file.
   *                               Default: 1 second.
   */
  DataLogger(const std::string& data_file_path, int64_t period_ns = 10'000'000, int64_t write_data_interval_ns = 1'000'000'000);
  ~DataLogger() override;

  // TODO: make this class a template on T and use perfect forwarding here...
  /**
   * This method should only be called by one consumer (thread). It pushes data
   * to be logged into a file for later consumption.
   */
  bool EmplaceData(double timestamp, double output_value) noexcept;

 protected:
  void Run() final;

 private:
  void WriteAndEmptyDataFromBuffer() noexcept;

  void ReadAndLogMessageCount() noexcept;

  void IncrementMessageCount(uint32_t successful_message_count) noexcept;
};

#endif
