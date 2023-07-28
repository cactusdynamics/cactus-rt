#include "cactus_rt/tracing/sink.h"

using cactus_tracing::vendor::perfetto::protos::Trace;

namespace cactus_rt::tracing {
FileSink::FileSink(const char* filename) : file_(filename, std::ios::out | std::ios::trunc | std::ios::binary) {}

bool FileSink::Write(const Trace& trace) {
  return trace.SerializeToOstream(&file_);
}
}  // namespace cactus_rt::tracing
