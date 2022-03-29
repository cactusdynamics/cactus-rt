#include "data_monitor.h"

namespace rt_demo {
bool DataMonitor::LogOutput(int64_t time, int output) {
  std::pair<int64_t, int> data{time, output};

  auto success = hf_output_fifo_.push(data);

  // TODO: possibly optimize out these statistics tracking code.
  if (!success) {
    ++hf_output_fifo_push_failed_.first;
  }

  ++hf_output_fifo_push_failed_.second;

  return success;
}

void DataMonitor::Run() noexcept {
  while (true) {
  }
}
}  // namespace rt_demo
