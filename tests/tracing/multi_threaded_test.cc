#include <cactus_rt/rt.h>
#include <gtest/gtest.h>
#include <quill/detail/LogManager.h>

#include <memory>

#include "helpers/assert_helpers.h"
#include "helpers/mock_sink.h"
#include "helpers/mock_threads.h"
#include "helpers/utils.h"

namespace {
const char* kAppName = "TestApp";
}

using namespace std::chrono_literals;

namespace cactus_rt {

class MultiThreadTracingTest : public ::testing::Test {
  static cactus_rt::AppConfig CreateAppConfig() {
    cactus_rt::AppConfig config;
    return config;
  }

 protected:
  cactus_rt::App                     app_;
  std::shared_ptr<MockRegularThread> regular_thread_;
  std::shared_ptr<MockCyclicThread>  cyclic_thread_;
  std::shared_ptr<MockSink>          sink_;

 public:
  MultiThreadTracingTest()
      : app_(kAppName, CreateAppConfig()),
        regular_thread_(std::make_shared<MockRegularThread>()),
        cyclic_thread_(std::make_shared<MockCyclicThread>()),
        sink_(std::make_shared<MockSink>()) {}

 protected:
  void SetUp() override {
    app_.StartTraceSession(sink_);
  }

  void TearDown() override {
    app_.RequestStop();
    app_.Join();

    // Need to stop it for every test as every app.Start() will start a background thread.
    quill::detail::LogManagerSingleton::instance().log_manager().stop_backend_worker();
  }
};

TEST_F(MultiThreadTracingTest, TraceFromMultipleThreads) {
  app_.RegisterThread(regular_thread_);
  app_.RegisterThread(cyclic_thread_);

  app_.Start();

  regular_thread_->RunOneIteration([](MockRegularThread* self) {
    self->TracerForTest().InstantEvent("Event1");
    WasteTime(std::chrono::microseconds(1000));
  });

  cyclic_thread_->Join();
  regular_thread_->RequestStop();
  regular_thread_->Join();

  app_.StopTraceSession();

  auto traces = sink_->LoggedTraces();
  auto packets = GetPacketsFromTraces(traces);
  ASSERT_EQ(packets.size(), 44);  // 3 track descriptor + 20 spans + 1 event

  AssertIsProcessTrackDescriptor(*packets[0], kAppName);
  const auto process_track_uuid = packets[0]->track_descriptor().uuid();

  auto traces_grouped = GetPacketsGroupByThreads(traces);
  ASSERT_EQ(traces_grouped.size(), 2);

  const auto& regular_thread_traces = traces_grouped.at(kRegularThreadName);
  const auto& cyclic_thread_traces = traces_grouped.at(kCyclicThreadName);

  ASSERT_EQ(regular_thread_traces.size(), 2);
  ASSERT_EQ(cyclic_thread_traces.size(), 41);

  AssertIsThreadTrackDescriptor(*regular_thread_traces[0], kRegularThreadName, process_track_uuid);
  const auto regular_thread_track_uuid = regular_thread_traces[0]->track_descriptor().uuid();

  AssertIsTrackEventInstant(*regular_thread_traces[1], regular_thread_track_uuid);

  auto event_names = GetInternedEventNames(*regular_thread_traces[1]);
  ASSERT_EQ(event_names.size(), 1);

  const auto event1_iid = event_names.at("Event1");
  ASSERT_GT(event1_iid, 0);

  AssertTrackEventHasIid(*regular_thread_traces[1], event1_iid, 0);

  const auto regular_thread_sequence_id = regular_thread_traces[1]->trusted_packet_sequence_id();

  AssertIsThreadTrackDescriptor(*cyclic_thread_traces[0], kCyclicThreadName, process_track_uuid);
  const auto cyclic_thread_track_uuid = cyclic_thread_traces[0]->track_descriptor().uuid();

  AssertIsTrackEventSliceBegin(*cyclic_thread_traces[1], cyclic_thread_track_uuid);

  event_names = GetInternedEventNames(*cyclic_thread_traces[1]);
  ASSERT_EQ(event_names.size(), 1);

  const auto loop_iid = event_names.at("Loop");
  ASSERT_GT(loop_iid, 0);

  auto event_categories = GetInternedEventCategories(*cyclic_thread_traces[1]);
  ASSERT_EQ(event_categories.size(), 1);

  const auto cactusrt_category_iid = event_categories.at("cactusrt");
  ASSERT_GT(cactusrt_category_iid, 0);

  AssertTrackEventHasIid(*cyclic_thread_traces[1], loop_iid, cactusrt_category_iid);

  auto sequence_id = cyclic_thread_traces[1]->trusted_packet_sequence_id();
  ASSERT_NE(regular_thread_sequence_id, sequence_id);

  for (size_t i = 0; i < 20; i++) {
    auto begin_idx = 1 + (i * 2);
    auto end_idx = 1 + (i * 2) + 1;

    AssertIsTrackEventSliceBegin(*cyclic_thread_traces[begin_idx], cyclic_thread_track_uuid, sequence_id);
    if (i != 0) {
      // The first packet will have interned data and we checked it already with the previous block
      AssertTrackEventHasNoInternedData(*cyclic_thread_traces[begin_idx]);
    }

    AssertTrackEventHasIid(*cyclic_thread_traces[begin_idx], loop_iid, cactusrt_category_iid);
    AssertIsTrackEventSliceEnd(*cyclic_thread_traces[end_idx], cyclic_thread_track_uuid, sequence_id);
  }
}

TEST_F(MultiThreadTracingTest, CyclicThreadTracesLoop) {
  // TODO: move the configuration for the number of loops and time per loop here
  // so it's easier to check the assertions are working.
  app_.RegisterThread(cyclic_thread_);
  app_.Start();

  // The cyclic thread should shutdown on its own.
  app_.Join();
  app_.StopTraceSession();

  auto traces = sink_->LoggedTraces();
  auto packets = GetPacketsFromTraces(traces);
  ASSERT_EQ(packets.size(), 42);  // 2 track descriptor + 20 spans

  AssertIsProcessTrackDescriptor(*packets[0], kAppName);
  const auto process_track_uuid = packets[0]->track_descriptor().uuid();

  AssertIsThreadTrackDescriptor(*packets[1], kCyclicThreadName, process_track_uuid);
  const auto thread_track_uuid = packets[1]->track_descriptor().uuid();

  AssertIsTrackEventSliceBegin(*packets[2], thread_track_uuid);

  auto event_names = GetInternedEventNames(*packets[2]);
  ASSERT_EQ(event_names.size(), 1);

  const auto loop_iid = event_names.at("Loop");
  ASSERT_GT(loop_iid, 0);

  auto event_categories = GetInternedEventCategories(*packets[2]);
  ASSERT_EQ(event_categories.size(), 1);

  const auto cactusrt_category_iid = event_categories.at("cactusrt");
  ASSERT_GT(cactusrt_category_iid, 0);

  AssertTrackEventHasIid(*packets[2], loop_iid, cactusrt_category_iid);

  auto sequence_id = packets[2]->trusted_packet_sequence_id();

  for (size_t i = 0; i < 20; i++) {
    auto begin_idx = 2 + (i * 2);
    auto end_idx = 2 + (i * 2) + 1;

    AssertIsTrackEventSliceBegin(*packets[begin_idx], thread_track_uuid);
    if (i != 0) {
      // The first packet will have interned data and we checked it already with the previous block
      AssertTrackEventHasNoInternedData(*packets[begin_idx]);
    }

    AssertTrackEventHasIid(*packets[begin_idx], loop_iid, cactusrt_category_iid);
    AssertIsTrackEventSliceEnd(*packets[end_idx], thread_track_uuid, sequence_id);
  }
}

TEST_F(MultiThreadTracingTest, CyclicThreadTracesSleepAndDoesNotTraceLoopIfConfigured) {
  cactus_rt::ThreadTracerConfig tracer_config;
  tracer_config.trace_loop = false;
  tracer_config.trace_overrun = false;
  tracer_config.trace_sleep = true;

  const char* thread_name = "CustomCyclicThread";

  auto cyclic_thread = std::make_shared<MockCyclicThread>(
    thread_name,
    tracer_config
  );

  app_.RegisterThread(cyclic_thread);
  app_.Start();

  // The cyclic thread should shutdown on its own.
  app_.Join();
  app_.StopTraceSession();

  auto traces = sink_->LoggedTraces();
  auto packets = GetPacketsFromTraces(traces);

  ASSERT_EQ(packets.size(), 2 + 19 * 2);  // 2 track descriptor + 19 spans of sleeps. Note the last iteration doesn't have a sleep at the end.

  AssertIsProcessTrackDescriptor(*packets[0], kAppName);
  const auto process_track_uuid = packets[0]->track_descriptor().uuid();

  AssertIsThreadTrackDescriptor(*packets[1], thread_name, process_track_uuid);
  const auto thread_track_uuid = packets[1]->track_descriptor().uuid();

  AssertIsTrackEventSliceBegin(*packets[2], thread_track_uuid);

  auto event_names = GetInternedEventNames(*packets[2]);
  ASSERT_EQ(event_names.size(), 1);

  const auto sleep_iid = event_names.at("Sleep");
  ASSERT_GT(sleep_iid, 0);

  auto event_categories = GetInternedEventCategories(*packets[2]);
  ASSERT_EQ(event_categories.size(), 1);

  const auto cactusrt_category_iid = event_categories.at("cactusrt");
  ASSERT_GT(cactusrt_category_iid, 0);

  AssertTrackEventHasIid(*packets[2], sleep_iid, cactusrt_category_iid);

  auto sequence_id = packets[2]->trusted_packet_sequence_id();

  for (size_t i = 0; i < 19; i++) {
    auto begin_idx = 2 + (i * 2);
    auto end_idx = 2 + (i * 2) + 1;

    AssertIsTrackEventSliceBegin(*packets[begin_idx], thread_track_uuid, sequence_id);
    if (i != 0) {
      // The first packet will have interned data and we checked it already with the previous block
      AssertTrackEventHasNoInternedData(*packets[begin_idx]);
    }

    AssertTrackEventHasIid(*packets[begin_idx], sleep_iid, cactusrt_category_iid);

    AssertIsTrackEventSliceEnd(*packets[end_idx], thread_track_uuid, sequence_id);

    // 100 Hz = 10ms loop.
    // The loop wastes 20us of time.
    // So we expect sleeping at least 5ms up to 15ms seems safe for testing?...
    AssertTrackEventDuration(*packets[begin_idx], *packets[end_idx], 5'000'000, 15'000'000);
  }
}

TEST_F(MultiThreadTracingTest, CyclicThreadTracesLoopOverrun) {
  cactus_rt::ThreadTracerConfig tracer_config;
  tracer_config.trace_loop = false;
  tracer_config.trace_overrun = true;
  tracer_config.trace_sleep = false;

  const char* thread_name = "CustomCyclicThread";

  auto cyclic_thread = std::make_shared<MockCyclicThread>(
    thread_name,
    tracer_config,
    [](int64_t num_iterations) {
      if (num_iterations == 10) {
        WasteTime(20ms);  // Should trigger overrun.
      }
    }
  );

  app_.RegisterThread(cyclic_thread);
  app_.Start();

  // The cyclic thread should shutdown on its own.
  app_.Join();
  app_.StopTraceSession();

  auto traces = sink_->LoggedTraces();
  auto packets = GetPacketsFromTraces(traces);

  ASSERT_EQ(packets.size(), 2 + 1);  // 2 track descriptor + 1 instant event

  AssertIsProcessTrackDescriptor(*packets[0], kAppName);
  const auto process_track_uuid = packets[0]->track_descriptor().uuid();

  AssertIsThreadTrackDescriptor(*packets[1], thread_name, process_track_uuid);
  const auto thread_track_uuid = packets[1]->track_descriptor().uuid();

  AssertIsTrackEventInstant(*packets[2], thread_track_uuid);

  auto event_names = GetInternedEventNames(*packets[2]);
  ASSERT_EQ(event_names.size(), 1);

  const auto name_iid = event_names.at("LoopOverrun");
  ASSERT_GT(name_iid, 0);

  auto event_categories = GetInternedEventCategories(*packets[2]);
  ASSERT_EQ(event_categories.size(), 1);

  const auto cactusrt_category_iid = event_categories.at("cactusrt");
  ASSERT_GT(cactusrt_category_iid, 0);

  AssertTrackEventHasIid(*packets[2], name_iid, cactusrt_category_iid);
}

}  // namespace cactus_rt
