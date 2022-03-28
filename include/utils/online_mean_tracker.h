#ifndef RT_DEMO_UTILS_ONLINE_MEAN_TRACKER_H_
#define RT_DEMO_UTILS_ONLINE_MEAN_TRACKER_H_

#include <cstdint>
#include <limits>

namespace rt_demo::utils {
class OnlineMeanTracker {
  double   min_;
  double   mean_;
  double   max_;
  uint64_t count_;

 public:
  OnlineMeanTracker() : min_(std::numeric_limits<double>::max()),
                        mean_(0.0),
                        max_(std::numeric_limits<double>::min()),
                        count_(0) {}

  void AddValue(double v) noexcept;

  double Min() const noexcept { return min_; }
  double Max() const noexcept { return max_; }
  double Mean() const noexcept { return mean_; }
  double Count() const noexcept { return count_; }
};
}  // namespace rt_demo::utils

#endif
