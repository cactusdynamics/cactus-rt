#include <cactus_rt/rt.h>
#include <perfetto.h>
#include <spdlog/spdlog.h>

#include <condition_variable>
#include <iostream>
#include <mutex>

// Perfetto definitions must be placed in main.cc file

// NOLINTBEGIN
PERFETTO_DEFINE_CATEGORIES(
  perfetto::Category("rt").SetDescription("Events from the RT thread"));

PERFETTO_TRACK_EVENT_STATIC_STORAGE();
// NOLINTEND

int NumFactors(int n) {
  int c = 0;
  for (int i = 1; i < n; i++) {
    if (n % i == 0) {
      c++;
    }
  }

  return c;
}

class RTThread : public cactus_rt::CyclicThread<cactus_rt::schedulers::Fifo> {
  int n_ = 0;

 public:
  RTThread() : cactus_rt::CyclicThread<cactus_rt::schedulers::Fifo>("CyclicThread", 1'000'000, /* Period */
                                                                    cactus_rt::schedulers::Fifo::Config{80 /* Priority */}) {}

  int GetResult() const {
    return n_;
  }

 protected:
  void BeforeRun() final {
    SPDLOG_INFO("Starting RT thread");
  }

  bool Loop(int64_t /*now*/) noexcept final {
    {
      TRACE_EVENT("rt", "Short");
      n_ += NumFactors(1'000);
    }

    {
      TRACE_EVENT("rt", "Medium");
      n_ += NumFactors(10'000);
    }

    {
      TRACE_EVENT("rt", "Long");
      n_ += NumFactors(100'000);
    }

    return false;
  }
};

class PerfettoTraceRecorder : public cactus_rt::Thread<cactus_rt::schedulers::Other> {
  std::unique_ptr<perfetto::TracingSession> tracing_session_;
  int                                       log_file_fd_;

  bool                    stop_tracing_ = false;
  std::mutex              stop_mutex_;
  std::condition_variable stop_cv_;

  bool                    ready = false;
  std::mutex              ready_mutex_;
  std::condition_variable ready_cv_;

 public:
  PerfettoTraceRecorder(const char* filename) : Thread("PerfettoTraceRecorder") {
    log_file_fd_ = open(filename, O_RDWR | O_CREAT | O_TRUNC, 0644);
    SPDLOG_INFO("starting perfetto trace recorder at {}", filename);
  }

  ~PerfettoTraceRecorder() override {
    close(log_file_fd_);
  }

  void RequestStop() noexcept override {
    // We override this method because we don't want to use the request_stop_
    // atomic variable as we want to notify the thread to stop tracing.  Since
    // this is a non-RT thread and the thread that calls this method will likely
    // not be a RT thread, a condition variable is fine.
    //
    // TODO: doesn't unique_lock throw an exception if it fails to acquire the lock...? that would conflict with noexcept
    std::unique_lock lck(stop_mutex_);
    stop_tracing_ = true;
    stop_cv_.notify_one();
  }

  void WaitForReady() {
    std::unique_lock lck(ready_mutex_);
    ready_cv_.wait(lck, [this] { return ready; });
  }

 protected:
  void Run() final {
    perfetto::TraceConfig trace_config;
    trace_config.add_buffers()->set_size_kb(16 * 1024);
    trace_config.set_write_into_file(true);
    trace_config.set_file_write_period_ms(1000);
    trace_config.set_flush_period_ms(1000);

    // Creates a data source for all track events.
    auto* data_source_config = trace_config.add_data_sources()->mutable_config();
    data_source_config->set_name("track_event");
    // By default, all non-debug categories are enabled.
    perfetto::protos::gen::TrackEventConfig track_event_config;
    track_event_config.add_enabled_categories("rt");
    data_source_config->set_track_event_config_raw(track_event_config.SerializeAsString());

    // NewTrace must be called after tracing config? Otherwise there's a segfault
    tracing_session_ = perfetto::Tracing::NewTrace();
    tracing_session_->Setup(trace_config, log_file_fd_);
    tracing_session_->StartBlocking();

    SPDLOG_INFO("tracing started");

    {
      std::unique_lock lck(ready_mutex_);
      ready = true;
      ready_cv_.notify_one();
    }

    {
      std::unique_lock lck(stop_mutex_);
      stop_cv_.wait(lck, [this] { return stop_tracing_; });
    }

    tracing_session_->StopBlocking();
    SPDLOG_INFO("tracing stopped");
  }
};

class RTApp : public cactus_rt::App {
  RTThread              rt_thread_;
  PerfettoTraceRecorder trace_recorder_thread_;

 public:
  RTApp() : trace_recorder_thread_("example.perfetto-trace") {
    SetupPerfettoTracing();
    RegisterThread(rt_thread_);
  }

  void Start() override {
    // If perfetto becomes a part of cactus RT, we can remove some of this.
    SPDLOG_DEBUG("Starting application");

    LockMemory();
    ReserveHeap();

    auto start_monotonic_time_ns = cactus_rt::NowNs();
    auto start_wall_time_ns = cactus_rt::WallNowNs();

    // Need to start the trace recorder first otherwise it might miss the beginning.
    trace_recorder_thread_.Start(start_monotonic_time_ns, start_wall_time_ns);
    trace_recorder_thread_.WaitForReady();

    StartRegisteredThreads(start_monotonic_time_ns, start_wall_time_ns);
  }

  void Stop() {
    rt_thread_.RequestStop();
    rt_thread_.Join();
    trace_recorder_thread_.RequestStop();
    trace_recorder_thread_.Join();
  }

  int Result() const {
    return rt_thread_.GetResult();
  }

 private:
  void SetupPerfettoTracing() {
    perfetto::TracingInitArgs args;
    args.backends = perfetto::kInProcessBackend;
    // If I specify the system backend, the loop executes slower and also no trace data is recorded?
    // TODO: figure out why. Specific the slower loop doesn't seem good.
    // args.backends |= perfetto::kSystemBackend;

    perfetto::Tracing::Initialize(args);
    perfetto::TrackEvent::Register();
  }
};

int main() {
  RTApp app;

  constexpr unsigned int time = 10;

  app.Start();
  sleep(time);
  app.Stop();

  std::cout << "final: " << app.Result() << "\n";

  return 0;
}
