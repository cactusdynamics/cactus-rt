#include "cactus_rt/tracing/tracing_enabled.h"

namespace cactus_rt::tracing {
std::atomic_bool tracing_enabled = CACTUS_RT_TRACING_STARTS_ENABLED;
}
