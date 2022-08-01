#ifndef RT_DEMO_EXAMPLES_MESSAGE_PASSING_EXAMPLE_DATA_LOGGER_H_
#define RT_DEMO_EXAMPLES_MESSAGE_PASSING_EXAMPLE_DATA_LOGGER_H_

#include <cactus_rt/thread.h>
#include <spdlog/spdlog.h>

#include <atomic>
#include <boost/lockfree/spsc_queue.hpp>
#include <filesystem>
#include <fstream>
#include <string>
#include <vector>

using boost::lockfree::spsc_queue;

struct OutputData {
  int64_t timestamp;
  double  output_value;
};

class DataLogger : public cactus_rt::Thread {
  constexpr static int kQueueCapacity = 8 * 1024;  // This is over 8 seconds of data. Should never be full.

  std::atomic_bool should_stop_;
  int64_t          period_us_;
  double           write_data_interval_seconds_;

  // https://www.boost.org/doc/libs/1_56_0/doc/html/boost/lockfree/spsc_queue.html
  // When full: reject additional push with returning false. This might be OK.
  // When empty: will return nothing on pop. Really, we want the data monitor
  // to block here, tho.
  //
  // https://stackoverflow.com/questions/22486552/boostlockfreespsc-queue-busy-wait-strategy-is-there-a-blocking-pop
  //
  // TODO: could probably use a dynamically allocated capacity as it would be
  // constructed on initialization.
  spsc_queue<OutputData, boost::lockfree::capacity<kQueueCapacity>> data_fifo_;
  std::pair<size_t, size_t>                                         data_fifo_push_failed_count_;
  std::vector<OutputData>                                           data_buffer_;

  std::ofstream data_file_;

 public:
  /**
   * Creates a new data logger thread.
   *
   * @param data_file_path The path to the CSV file to be saved.
   * @param period_us The period in us at which the data logger thread will run
   *                  at. Default: 10000 for 10ms. No good reason for this
   *                  value other than a guess that it might reduce scheduler
   *                  load? Probably not as this thread is a normal thread.
   * @param write_data_interval_seconds The interval in seconds at which the
   *                                    data is written to the CSV file.
   *                                    Default: 1 second.
   */
  DataLogger(const std::string& data_file_path,
             int64_t            period_us = 10'000,
             double             write_data_interval_seconds = 1.0);

  virtual ~DataLogger() {
    data_file_.close();
  }

  /**
   * This method should only be called by one consumer (thread). It pushes data
   * to be logged into a file for later consumption.
   *
   * @param data The data to be logged.
   * @returns success if the data is written into the buffer, false otherwise.
   */
  bool LogData(const OutputData& data) noexcept;

  /**
   * Requests the data logger to stop
   */
  void RequestStop() noexcept {
    should_stop_.store(true);
  }

  /**
   * Should only be called after the thread has joined, otherwise there's a
   * chance of data race.
   *
   * @returns the number of times push has failed and the number of times pushed in a std::pair
   */
  std::pair<size_t, size_t> LogDataFailedCount() const noexcept {
    return data_fifo_push_failed_count_;
  }

 protected:
  void Run() final;

 private:
  void WriteData() noexcept;
};

#endif
