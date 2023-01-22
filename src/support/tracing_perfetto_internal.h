// This is needed because users of cactus_rt will need to set this, while
// cactus_rt internally doesn't.
//
// This whole file is a hack, including the tracing_common.h and
// tracing_perfetto.h header files split. If the below feature is used, chances
// are none of this is needed.
//
// TODO: replace this solution with https://github.com/google/perfetto/commit/6020a92b81bb64bf66b99cf85d37eab2f8ded9fb
#define PERFETTO_TRACK_EVENT_NAMESPACE cactus_rt_perfetto
#include "cactus_rt/support/tracing_perfetto.h"

PERFETTO_DEFINE_CATEGORIES(
  perfetto::Category(cactus_rt::kTracingCategory).SetDescription("Events from the cactus-rt framework"));
