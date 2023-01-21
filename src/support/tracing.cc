#include "cactus_rt/support/tracing.h"

#include <fcntl.h>
#include <spdlog/spdlog.h>
#include <sys/stat.h>
#include <sys/types.h>

#include <cstring>

namespace cactus_rt {

TracerParameters TracerParameters::FromEnv() {
  TracerParameters params;

  // TODO: FIX ME BEFORE MERGE: read the parameters from the environment

  return params;
}
}  // namespace cactus_rt

#ifdef ENABLE_TRACING

// NOLINTBEGIN
// TODO: we should switch to PERFETTO_DEFINE_CATEGORIES_IN_NAMESPACE for Perfetto v32
PERFETTO_DEFINE_CATEGORIES(
  perfetto::Category(cactus_rt::kTracingCategory).SetDescription("Events from the cactus-rt framework"));

PERFETTO_TRACK_EVENT_STATIC_STORAGE();
// NOLINTEND

namespace cactus_rt {
InProcessTracer::InProcessTracer(const char* filename, const TracerParameters& params) : filename_(filename) {
  perfetto::TracingInitArgs args;
  args.backends = perfetto::kInProcessBackend;
  // If I specify the system backend, the loop executes slower and also no trace data is recorded?
  // TODO: figure out why. Specifically the slower loop doesn't seem good.
  // args.backends |= perfetto::kSystemBackend;

  perfetto::Tracing::Initialize(args);
  PERFETTO_TRACK_EVENT_NAMESPACE::TrackEvent::Register();

  log_file_fd_ = open(filename, O_RDWR | O_CREAT | O_TRUNC, 0644);
  if (log_file_fd_ == -1) {
    throw std::runtime_error{std::string("failed to open log file: ") + std::strerror(errno)};
  }

  trace_config_.add_buffers()->set_size_kb(params.bufsize);
  trace_config_.set_write_into_file(true);
  trace_config_.set_file_write_period_ms(params.file_write_period_ms);
  trace_config_.set_flush_period_ms(params.flush_period_ms);

  auto* data_source_config = trace_config_.add_data_sources()->mutable_config();
  data_source_config->set_name("track_event");

  // By default, all non-debug categories are enabled.
  perfetto::protos::gen::TrackEventConfig track_event_config;
  track_event_config.add_enabled_categories("*");
  data_source_config->set_track_event_config_raw(track_event_config.SerializeAsString());

  // NewTrace must be called after tracing config? Otherwise there's a segfault
  tracing_session_ = perfetto::Tracing::NewTrace();
  tracing_session_->Setup(trace_config_, log_file_fd_);
}

InProcessTracer::~InProcessTracer() {
  auto ret = close(log_file_fd_);
  if (ret != 0) {
    SPDLOG_ERROR("Failed to close tracing file: {}", std::strerror(errno));
  }
}

void InProcessTracer::Start() {
  tracing_session_->StartBlocking();
  SPDLOG_WARN("Tracing has started via Perfetto and logging to {}.", filename_);
  SPDLOG_WARN("While tracing overhead should be low, it should not be used in release builds at this time.");
  SPDLOG_WARN("Tracing can be disabled by compiling cactus_rt with ENABLE_TRACING=OFF.");
}

void InProcessTracer::Stop() {
  tracing_session_->StopBlocking();
  SPDLOG_WARN("Tracing has stopped.");
}
}  // namespace cactus_rt
#endif
