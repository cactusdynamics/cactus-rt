#ifndef CACTUS_RT_EXAMPLES_ICEORYX_EXAMPLE_DATA_H_
#define CACTUS_RT_EXAMPLES_ICEORYX_EXAMPLE_DATA_H_

#include <cstdint>

struct Data {
  int64_t t;
  int64_t counter = 0;
};

#endif