#include "data_monitor.h"

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
  while (true) {
    // If write_data_interval_ passed, call WriteData, which writes all data.

    // Pop from both queues.

    // If both queue's empty, sleep for 1ms (configurable, maybe should be
    // 500us) to allow for catchup as busy waiting take a lot of resources and
    // we can fall behind a little bit here.

    // Perform double buffering swap to display control parameters
  }
}
}  // namespace rt_demo
