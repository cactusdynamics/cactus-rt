#ifndef CACTUS_RT_TRACING_SINK_H_
#define CACTUS_RT_TRACING_SINK_H_

namespace cactus_rt::tracing {
class Sink {
 public:
  virtual ~Sink() = default;
};

class FileSink : public Sink {
 public:
  explicit FileSink(const char* /*filename*/) {}
};
}  // namespace cactus_rt::tracing

#endif
