#include "data_logger.h"

#include <rt/utils.h>

#include <chrono>
#include <iomanip>
#include <thread>

DataLogger::DataLogger(const std::string& data_file_path,
                       int64_t            period_us,
                       double             write_data_interval_seconds)
    : Thread("DataLogger", 0, SCHED_OTHER),
      should_stop_(false),
      period_us_(period_us),
      write_data_interval_seconds_(write_data_interval_seconds),
      data_fifo_push_failed_count_(0, 0) {
  data_file_.open(data_file_path);
  if (!data_file_.is_open()) {
    throw std::runtime_error{"failed to open data file"};
  }

  // Have the same capacity as the queue to ensure that reading the queue
  // will work every time.
  data_buffer_.reserve(kQueueCapacity);
}

bool DataLogger::LogData(const OutputData& data) noexcept {
  auto success = data_fifo_.push(data);

  if (!success) {
    ++data_fifo_push_failed_count_.first;
  }

  ++data_fifo_push_failed_count_.second;
  return success;
}

void DataLogger::Run() noexcept {
  auto last_data_write_time = rt::NowNs();

  OutputData data;

  while (true) {
    auto now = rt::NowNs();
    if (static_cast<double>(now - last_data_write_time) / 1'000'000'000 > write_data_interval_seconds_) {
      WriteData();
      last_data_write_time = now;
    }

    bool no_data = true;
    if (data_fifo_.pop(data)) {
      no_data = false;
      data_buffer_.push_back(data);
    }

    // If there is data, we keep popping from the queue.
    if (no_data) {
      // If there is no data, then we can check if we should stop
      if (should_stop_) {
        break;
      }

      // TODO: looking at the code for this, it seems safe as it just calls
      // nanosleep. That said, to make it explicit that we're not using the c++
      // thread library, should just refactor that code out in to Thread::sleep
      // here.
      std::this_thread::sleep_for(std::chrono::microseconds(period_us_));
    }
  }

  // Make sure any data in the buffer are written out.
  WriteData();
}

void DataLogger::WriteData() noexcept {
  spdlog::debug("writing {} data entries to file...", data_buffer_.size());
  for (const auto& data : data_buffer_) {
    // Log in microseconds
    data_file_ << std::setprecision(4) << std::fixed << (static_cast<double>(data.timestamp) / 1'000.0) << ", " << data.output_value << "\n";
  }

  data_buffer_.clear();
}
