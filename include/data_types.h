#ifndef RT_DEMO_DATA_TYPES_H_
#define RT_DEMO_DATA_TYPES_H_

#include <cstdint>

// Data types for the data passed between the threads.

namespace rt_demo {
/**
 * The output data for the high frequency controller.
 */
struct HFCOutput {
  int64_t timestamp;
  int     output;
};

/**
 * Some example control parameter to pass to the HFC.
 *
 * period: the period in nanoseconds of the wave function
 * threshold: the threshold value above which the output is 1, below which is 0.
 */
struct ControlParam {
  float period;
  float threshold;
};

struct LFCOutput {
  int          flag;
  ControlParam param;
};
}  // namespace rt_demo

#endif
