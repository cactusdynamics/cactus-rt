#include "rt_thread.h"

cactus_rt::CyclicThread::LoopControl RtThread::Loop(int64_t ellapsed_ns) noexcept {
  const double ellapsed_ms = static_cast<double>(ellapsed_ns) / 1'000'000.0;

  const double period = 1000.0;
  const double amplitude = 1.0;

  data_logger_->EmplaceData(ellapsed_ms, amplitude * cos(2 * M_PI / period * ellapsed_ms));

  ++iterations_;
  return iterations_ >= max_iterations_ ? LoopControl::Stop : LoopControl::Continue;
}
