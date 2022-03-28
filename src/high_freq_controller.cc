#include "high_freq_controller.h"

#include <cmath>
#include <iostream>

namespace rt_demo {
bool HighFrequencyController::Loop() noexcept {
  output_ += 1;
  return false;
}
}  // namespace rt_demo
