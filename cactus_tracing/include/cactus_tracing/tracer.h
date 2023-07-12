#ifndef CACTUS_TRACING_TRACER_H_
#define CACTUS_TRACING_TRACER_H_

#include <cstdint>
#include <fstream>
#include <memory>
#include <mutex>
#include <thread>
#include <vector>

#include "thread_tracer.h"
#include "trace.pb.h"

namespace cactus_tracing {

/**
 * The tracer for the process. It manages all the ThreadTracers and also manages
 * the background thread for writing out to the trace files.
 */
class Tracer {
  const char* process_name_;
  int32_t     process_pid_;
  uint64_t    process_uuid_;

  const char*  output_filename_;
  std::fstream output_file_;

  // The mutex is for adding tracers into the thread_tracers_ vector.
  std::mutex                                 mutex_;
  std::vector<std::shared_ptr<ThreadTracer>> thread_tracers_;

  std::vector<cactus_tracing::vendor::perfetto::protos::Trace> thread_descriptor_trace_packets_;

  std::thread      background_thread_;
  std::atomic_bool stop_requested_ = false;

  Tracer(const char* process_name, const char* output_filename);

 public:
  static Tracer& Instance(const char* process_name, const char* output_filename) {
    static Tracer tracer(process_name, output_filename);
    return tracer;
  }

  // No copy
  Tracer(const Tracer&) = delete;
  Tracer& operator=(const Tracer&) = delete;

  // No move
  Tracer(Tracer&&) noexcept = delete;
  Tracer& operator=(Tracer&&) noexcept = delete;

  void StartBackgroundThread();
  void StopBackgroundThread();
  void JoinBackgroundThread();
  void RegisterThreadTracer(std::shared_ptr<ThreadTracer> thread_tracer);

 private:
  void BackgroundThreadMain();

  // Return false on failure to write...
  bool WriteProcessDescriptorPacket();

  bool WriteTrace(const cactus_tracing::vendor::perfetto::protos::Trace& trace);

  bool EmptyTrackDescriptorPackets();

  cactus_tracing::vendor::perfetto::protos::Trace CreateThreadDescriptorPacket(const ThreadTracer& thread_tracer) const;
  cactus_tracing::vendor::perfetto::protos::Trace CreateTrackEventPacket(const TrackEvent& track_event, const ThreadTracer& thread_tracer) const;
};
}  // namespace cactus_tracing

#endif
