#ifndef CACTUS_RT_LOGGER_H_
#define CACTUS_RT_LOGGER_H_

#include "quill/Frontend.h"
#include "quill/LogMacros.h"
#include "quill/core/Common.h"
#include "quill/std/Array.h"
#include "quill/std/Chrono.h"
#include "quill/std/Deque.h"
#include "quill/std/FilesystemPath.h"
#include "quill/std/ForwardList.h"
#include "quill/std/List.h"
#include "quill/std/Map.h"
#include "quill/std/Optional.h"
#include "quill/std/Pair.h"
#include "quill/std/Set.h"
#include "quill/std/Tuple.h"
#include "quill/std/UnorderedMap.h"
#include "quill/std/UnorderedSet.h"
#include "quill/std/Vector.h"
#include "quill/std/WideString.h"

namespace cactus_rt {
struct FrontendOptions {
  // Set the queue to BoundedDropping to prevent allocation
  static constexpr quill::QueueType queue_type = quill::QueueType::BoundedDropping;
  static constexpr uint32_t         initial_queue_capacity = 131'072;
  static constexpr int32_t          blocking_queue_retry_interval_ns = 800;
  static constexpr bool             huge_pages_enabled = false;
};

using Frontend = quill::FrontendImpl<FrontendOptions>;
using Logger = quill::LoggerImpl<FrontendOptions>;
}  // namespace cactus_rt
#endif
