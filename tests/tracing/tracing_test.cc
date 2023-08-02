#include <gtest/gtest.h>

#include <memory>

#include "cactus_rt/app.h"
#include "mock_sink.h"
#include "mock_threads.h"
#include "utils.h"

constexpr const char* kAppName = "TracingTestApp";
constexpr const char* kRegularThreadName = "RegularThread";

// Need a few things:
// A simple app with probably 2 threads (one cyclic and one not)
// Threads needs to run at configurable intervals (smallish)
// Threads needs to trace some time wasting events
// Threads needs to stop at configurable time
// Threads needs to keep track at the number of event it sent to the tracer (probably need a lock in the Loop function, but it's OK as this is a non-RT test code anyway).

class TracingTest : public ::testing::Test {
  static cactus_rt::AppConfig CreateTracingAppConfig() {
    cactus_rt::AppConfig config;
    config.name = kAppName;
    return config;
  }

 protected:
  cactus_rt::App                     app_;
  std::shared_ptr<MockRegularThread> regular_thread_;
  std::shared_ptr<MockSink>          sink_;

 public:
  TracingTest()
      : app_(CreateTracingAppConfig()) {}

 protected:
  void SetUp() override {
    cactus_rt::ThreadConfig config;
    config.name = kRegularThreadName;
    config.scheduler_config.emplace<cactus_rt::OtherThreadConfig>();

    regular_thread_ = std::make_shared<MockRegularThread>(config);
    app_.RegisterThread(regular_thread_);
    app_.StartTraceSession();

    sink_ = std::make_shared<MockSink>();
    app_.RegisterTraceSink(sink_);

    app_.Start();
  }

  void TearDown() override {
    app_.RequestStop();
    app_.Join();
  }
};

using cactus_tracing::vendor::perfetto::protos::TracePacket;
using cactus_tracing::vendor::perfetto::protos::TrackEvent_Type_TYPE_INSTANT;
using cactus_tracing::vendor::perfetto::protos::TrackEvent_Type_TYPE_SLICE_BEGIN;
using cactus_tracing::vendor::perfetto::protos::TrackEvent_Type_TYPE_SLICE_END;

TEST_F(TracingTest, WithSpan) {
  regular_thread_->RunOneIteration([](MockRegularThread* self) {
    auto span = self->TracerForTest().WithSpan("TestEvent", "category");
    WasteTime(std::chrono::microseconds(1000));
  });

  app_.StopTraceSession();

  auto                            traces = sink_->LoggedTraces();
  std::vector<const TracePacket*> packets;

  for (const auto& trace : traces) {
    for (int i = 0; i < trace.packet_size(); i++) {
      const TracePacket* packet = &trace.packet(i);
      packets.push_back(packet);
    }
  }

  ASSERT_EQ(packets.size(), 4);

  // First packet is a process track descriptor
  ASSERT_TRUE(packets[0]->has_track_descriptor());
  const auto& track_descriptor0 = packets[0]->track_descriptor();
  ASSERT_TRUE(track_descriptor0.has_process());
  ASSERT_TRUE(track_descriptor0.process().has_process_name());
  ASSERT_EQ(track_descriptor0.process().process_name(), kAppName);
  ASSERT_EQ(track_descriptor0.process().pid(), getpid());

  const auto process_track_uuid = track_descriptor0.uuid();
  ASSERT_TRUE(process_track_uuid > 0);

  // Second packet is a thread track descriptor
  ASSERT_TRUE(packets[1]->has_track_descriptor());
  const auto& track_descriptor1 = packets[1]->track_descriptor();
  ASSERT_EQ(track_descriptor1.parent_uuid(), process_track_uuid);
  ASSERT_TRUE(track_descriptor1.has_thread());

  ASSERT_EQ(track_descriptor1.thread().pid(), getpid());
  ASSERT_TRUE(track_descriptor1.thread().has_thread_name());
  ASSERT_EQ(track_descriptor1.thread().thread_name(), kRegularThreadName);
  ASSERT_TRUE(track_descriptor1.thread().tid() > 0);

  auto thread_track_uuid = track_descriptor1.uuid();
  ASSERT_TRUE(thread_track_uuid > 0);

  // Third packet is the slice begin
  ASSERT_TRUE(packets[2]->has_track_event());
  const auto& track_event_start = packets[2]->track_event();

  ASSERT_EQ(track_event_start.type(), TrackEvent_Type_TYPE_SLICE_BEGIN);
  ASSERT_TRUE(track_event_start.has_name());
  ASSERT_EQ(track_event_start.name(), "TestEvent");

  ASSERT_EQ(track_event_start.categories_size(), 1);
  ASSERT_EQ(track_event_start.categories(0), "category");

  ASSERT_EQ(track_event_start.track_uuid(), thread_track_uuid);

  auto sequence_id = packets[2]->trusted_packet_sequence_id();
  ASSERT_TRUE(sequence_id > 0);

  // Fourth packet is slice end
  ASSERT_TRUE(packets[3]->has_track_event());
  const auto& track_event_end = packets[3]->track_event();

  ASSERT_EQ(track_event_end.type(), TrackEvent_Type_TYPE_SLICE_END);
  ASSERT_FALSE(track_event_end.has_name());
  ASSERT_EQ(track_event_end.categories_size(), 0);
  ASSERT_EQ(track_event_end.track_uuid(), thread_track_uuid);

  ASSERT_EQ(packets[3]->trusted_packet_sequence_id(), sequence_id);
}

// Things to test:
// Spans work with name, category, etc.
// Nested spans work.
// Instant event works
// Trace session is started dynamically.
// Trace session is stopped and it is known we can ensure no further events are sent.
// No trace events are missed at the end of the session as everything is flushed.
// CPU affinity
// Dyamically adding and removing threads works (especially in terms of the track descriptors)
// Dynamically adding and removing sinks works  (especially in terms of track descriptors)
// Overflow behavior
// Sink write failure behavior

// Things to benchmark
// - The latency/throughput of Emit when tracing is on and off
// - The throughput of popping data from the queue....
