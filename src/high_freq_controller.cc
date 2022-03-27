#include "high_freq_controller.h"

#include <iostream>

namespace rt_demo {
void HighFrequencyController::Run() noexcept {
  while (state_ < 1000) {
    state_ += 10;
  }
}
}  // namespace rt_demo
