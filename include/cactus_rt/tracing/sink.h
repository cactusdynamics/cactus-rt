#ifndef CACTUS_RT_TRACING_SINK_H_
#define CACTUS_RT_TRACING_SINK_H_

#include <fstream>

#include "trace.pb.h"

namespace cactus_rt::tracing {
/**
 * @brief An arbitrary sink where trace packets can be written to.
 */
class Sink {
 public:
  virtual ~Sink() = 0;
  virtual bool Write(const cactus_tracing::vendor::perfetto::protos::Trace& trace) = 0;
};

/**
 * @brief A file sink where trace data is written to a file.
 */
class FileSink : public Sink {
  std::fstream file_;

 public:
  explicit FileSink(const char* filename);

  bool Write(const cactus_tracing::vendor::perfetto::protos::Trace& trace) final;
};
}  // namespace cactus_rt::tracing
#endif
