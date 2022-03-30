#include "data_monitor.h"

#include <spdlog/spdlog.h>

#include <chrono>
#include <thread>

#include "utils/utils.h"

namespace rt_demo {
bool DataMonitor::LogOutput(const HFCOutput& data) noexcept {
  auto success = hf_fifo_.push(data);

  // TODO: possibly optimize out these statistics tracking code.
  if (!success) {
    ++hf_fifo_push_failed_.first;
  }

  ++hf_fifo_push_failed_.second;

  return success;
}

void DataMonitor::Run() noexcept {
  auto last_data_write_time = Now();

  HFCOutput hf_data;

  while (true) {
    // If write_data_interval_ passed, call WriteData, which writes all data.
    auto now = Now();
    if (utils::TimespecDiffNanoseconds(now, last_data_write_time) / 1'000'000'000.0 > write_data_interval_) {
      WriteData();
      last_data_write_time = now;
    }

    // Pop from both queues.
    bool should_sleep = true;

    if (hf_fifo_.pop(hf_data)) {
      should_sleep = false;
      hf_data_buf_.push_back(hf_data);
    }

    // Perform double buffering swap to display control parameters

    // If both queue's empty, sleep for 1ms (configurable, maybe should be
    // 500us) to allow for catchup as busy waiting take a lot of resources and
    // we can fall behind a little bit here.

    if (should_sleep) {
      // TODO: looking at the code for this, it seems safe as it just calls
      // nanosleep. That said, to make it explicit that we're not using the c++
      // thread library, should just refactor that code out in to Thread::sleep
      // here.
      std::this_thread::sleep_for(std::chrono::microseconds(500));
    }
  }
}

void DataMonitor::WriteData() noexcept {
  spdlog::info("write data {}", hf_data_buf_.size());
  for (const auto& data : hf_data_buf_) {
    spdlog::info("{}\t{}", data.timestamp / 1'000.0, data.output);
  }

  hf_data_buf_.clear();
}
}  // namespace rt_demo
