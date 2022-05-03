#ifndef RT_DEMO_RT_LATENCY_TRACKING_H_
#define RT_DEMO_RT_LATENCY_TRACKING_H_

#include <array>
#include <cstdint>
#include <limits>

using std::size_t;

namespace rt {

class LatencyTracker {
 public:
  using HistogramArray = std::array<size_t, 11>;

 private:
  double min_ = std::numeric_limits<double>::max();
  double mean_ = 0.0;
  double max_ = std::numeric_limits<double>::min();
  size_t count_ = 0;

  HistogramArray histogram_ = {};

 public:
  void RecordValue(double v) noexcept;

  double Min() const noexcept { return min_; }
  double Mean() const noexcept { return mean_; }
  double Max() const noexcept { return max_; }
  size_t Count() const noexcept { return count_; }

  const HistogramArray Histogram() const noexcept { return histogram_; }
  void                 DumpToLogger() const;
};

}  // namespace rt

#endif
