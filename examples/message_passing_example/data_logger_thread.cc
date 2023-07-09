#include "data_logger_thread.h"

#include <chrono>

DataLogger::DataLogger(
  const std::string& data_file_path,
  int64_t            period_ns,
  int64_t            write_data_interval_ns
) : Thread<Other>("DataLogger"),
    period_ns_(period_ns),
    write_data_interval_ns_(write_data_interval_ns),
    queue_(kQueueCapacity),
    message_count_({0, 0}) {
  file_.open(data_file_path);
  if (!file_.is_open()) {
    throw std::runtime_error{"failed to open data file"};
  }

  // Have the same capacity as the queue to ensure that reading the queue
  // will work every time.
  data_buffer_.reserve(kQueueCapacity);
}

DataLogger::~DataLogger() {
  file_.close();
}

bool DataLogger::EmplaceData(double timestamp, double output_value) noexcept {
  // should always use the try_* method in the hot path, as these do not allocate
  const bool success = queue_.try_emplace(timestamp, output_value);
  if (success) {
    IncrementMessageCount(1);
  } else {
    IncrementMessageCount(0);
  }
  return success;
}

void DataLogger::Run() {
  auto last_data_write_time = cactus_rt::NowNs();

  OutputData data;

  while (true) {
    auto now = cactus_rt::NowNs();
    if (now - last_data_write_time > write_data_interval_ns_) {
      WriteAndEmptyDataFromBuffer();
      last_data_write_time = now;
    }

    bool no_data = true;
    if (queue_.try_dequeue(data)) {
      no_data = false;
      data_buffer_.push_back(data);  // Takes a copy of data here...
    }

    // If there is data, we keep popping from the queue.
    if (no_data) {
      // If there is no data, then we can check if we should stop
      if (this->StopRequested()) {
        break;
      }

      // TODO: looking at the code for this, it seems safe as it just calls
      // nanosleep. That said, to make it explicit that we're not using the c++
      // thread library, should just refactor that code out in to Thread::sleep
      // here.
      std::this_thread::sleep_for(std::chrono::nanoseconds(period_ns_));
    }
  }

  // Make sure any data in the buffer are written out.
  WriteAndEmptyDataFromBuffer();
}

void DataLogger::WriteAndEmptyDataFromBuffer() noexcept {
  LOG_INFO(Logger(), "writing {} data entries to file...", data_buffer_.size());

  ReadAndLogMessageCount();

  for (const auto& data : data_buffer_) {
    // Log in microseconds
    file_ << std::setprecision(4) << std::fixed << (static_cast<double>(data.timestamp) / 1'000.0) << ", " << data.output_value << "\n";
  }

  data_buffer_.clear();
}

void DataLogger::ReadAndLogMessageCount() noexcept {
  const auto current_count = message_count_.load();

  LOG_INFO(Logger(), "received {} messages and dropped {}", current_count.total_messages, current_count.total_messages - current_count.successful_messages);
}

// A demonstration of how to pass a small amount of data via std::atomic if it can be done in a lock free manner.
// This is called from the real-time thread. The loop is probably unnecessary
// because it must be the only thread that reads and writes to this variable..
// successful_message_count should be either 0 or 1...
void DataLogger::IncrementMessageCount(uint32_t successful_message_count) noexcept {
  auto                old_count = message_count_.load();
  decltype(old_count) new_count;

  do {
    new_count = old_count;
    new_count.successful_messages += successful_message_count;
    new_count.total_messages += 1;
  } while (!message_count_.compare_exchange_weak(old_count, new_count));
}
