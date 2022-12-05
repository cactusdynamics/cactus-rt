#include "rt_thread.h"

bool RtThread::Loop(int64_t ellapsed_ns) noexcept {
  double ellapsed_ms = static_cast<double>(ellapsed_ns) / 1'000'000.0;

  double period = 1000.0;
  double amplitude = 1.0;

  OutputData data{ellapsed_ns};

  data_logger_.LogData(data);

  ++iterations_;
  return iterations_ >= max_iterations_;
}
