#include "utils/online_mean_tracker.h"

namespace rt_demo::utils {
void OnlineMeanTracker::AddValue(double v) noexcept {
  if (v < min_) {
    min_ = v;
  }

  if (v > max_) {
    max_ = v;
  }

  ++count_;
  mean_ = mean_ * (count_ - 1) / count_ + v / count_;
}
}  // namespace rt_demo::utils
