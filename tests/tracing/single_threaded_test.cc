#include <cactus_rt/rt.h>
#include <gtest/gtest.h>
#include <quill/Backend.h>

#include <chrono>
#include <memory>
#include <thread>

#include "helpers/assert_helpers.h"
#include "helpers/mock_sink.h"
#include "helpers/mock_threads.h"
#include "helpers/utils.h"

namespace {
const char* kAppName = "TestApp";
}

namespace cactus_rt {

class SingleThreadTracingTest : public ::testing::Test {
  static cactus_rt::AppConfig CreateAppConfig() {
    cactus_rt::AppConfig config;
    return config;
  }

 protected:
  cactus_rt::App                     app_;
  std::shared_ptr<MockRegularThread> regular_thread_;
  std::shared_ptr<MockSink>          sink_;

 public:
  SingleThreadTracingTest()
      : app_(kAppName, CreateAppConfig()),
        regular_thread_(app_.CreateThread<MockRegularThread>()),
        sink_(std::make_shared<MockSink>()) {}

 protected:
  void SetUp() override {
    app_.StartTraceSession(sink_);  // TODO: make each test manually start the trace session!
    app_.Start();
    while (!regular_thread_->Started()) {
      std::this_thread::sleep_for(std::chrono::milliseconds(1));  // Not that efficient but OK
    }
  }

  void TearDown() override {
    app_.RequestStop();
    app_.Join();

    // Need to stop it for every test as every app.Start() will start a background thread.
    quill::Backend::stop();
  }
};

TEST_F(SingleThreadTracingTest, WithSpan) {
  regular_thread_->RunOneIteration([](MockRegularThread* self) {
    auto span = self->TracerForTest().WithSpan("TestEvent", "category");
    WasteTime(std::chrono::microseconds(1000));
  });

  app_.StopTraceSession();

  auto traces = sink_->LoggedTraces();
  auto packets = GetPacketsFromTraces(traces);
  ASSERT_EQ(packets.size(), 4);

  // First packet is a process track descriptor
  AssertIsProcessTrackDescriptor(*packets[0], kAppName);
  const auto process_track_uuid = packets[0]->track_descriptor().uuid();

  // Second packet is a thread track descriptor
  AssertIsThreadTrackDescriptor(*packets[1], kRegularThreadName, process_track_uuid);
  auto thread_track_uuid = packets[1]->track_descriptor().uuid();

  // Third packet is the slice begin
  AssertIsTrackEventSliceBegin(*packets[2], thread_track_uuid);
  auto sequence_id = packets[2]->trusted_packet_sequence_id();

  const auto event_names = GetInternedEventNames(*packets[2]);
  ASSERT_EQ(event_names.size(), 1);

  const auto event_name_iid = event_names.at("TestEvent");
  ASSERT_GT(event_name_iid, 0);

  const auto event_categories = GetInternedEventCategories(*packets[2]);
  ASSERT_EQ(event_categories.size(), 1);

  const auto category_iid = event_categories.at("category");
  ASSERT_GT(category_iid, 0);

  AssertTrackEventHasIid(*packets[2], event_name_iid, category_iid);

  // Fourth packet is slice end
  AssertIsTrackEventSliceEnd(*packets[3], thread_track_uuid, sequence_id);

  // Check duration is between 1000us to 10000us
  AssertTrackEventDuration(*packets[2], *packets[3], 1000000, 10000000);
}

TEST_F(SingleThreadTracingTest, WithSpanNested) {
  regular_thread_->RunOneIteration([](MockRegularThread* self) {
    auto span = self->TracerForTest().WithSpan("OuterEvent", "outer");

    {
      auto inner_span1 = self->TracerForTest().WithSpan("InnerEvent1", "inner");
      {
        auto inner_inner_span1 = self->TracerForTest().WithSpan("InnerInnerEvent1", "inner");
        WasteTime(std::chrono::microseconds(1000));
      }

      {
        auto inner_inner_span2 = self->TracerForTest().WithSpan("InnerInnerEvent2", "inner");
        WasteTime(std::chrono::microseconds(1000));
      }
    }

    {
      auto inner_span2 = self->TracerForTest().WithSpan("InnerEvent2", "inner");
      WasteTime(std::chrono::microseconds(2000));
    }
  });

  app_.StopTraceSession();

  auto traces = sink_->LoggedTraces();
  auto packets = GetPacketsFromTraces(traces);
  ASSERT_EQ(packets.size(), 12);

  AssertIsProcessTrackDescriptor(*packets[0], kAppName);
  const auto process_track_uuid = packets[0]->track_descriptor().uuid();

  AssertIsThreadTrackDescriptor(*packets[1], kRegularThreadName, process_track_uuid);
  auto thread_track_uuid = packets[1]->track_descriptor().uuid();

  // First OuterEvent, outer packet
  AssertIsTrackEventSliceBegin(*packets[2], thread_track_uuid);
  auto sequence_id = packets[2]->trusted_packet_sequence_id();

  auto event_names = GetInternedEventNames(*packets[2]);
  ASSERT_EQ(event_names.size(), 1);

  const auto outer_event_iid = event_names.at("OuterEvent");
  ASSERT_GT(outer_event_iid, 0);

  auto event_categories = GetInternedEventCategories(*packets[2]);
  ASSERT_EQ(event_categories.size(), 1);

  const auto outer_category_iid = event_categories.at("outer");
  ASSERT_GT(outer_category_iid, 0);

  AssertTrackEventHasIid(*packets[2], outer_event_iid, outer_category_iid);

  // First InnerEvent1, inner packet
  AssertIsTrackEventSliceBegin(*packets[3], thread_track_uuid, sequence_id);
  event_names = GetInternedEventNames(*packets[3]);
  ASSERT_EQ(event_names.size(), 1);

  const auto inner_event1_iid = event_names.at("InnerEvent1");
  ASSERT_GT(inner_event1_iid, 0);
  ASSERT_NE(inner_event1_iid, outer_event_iid);

  event_categories = GetInternedEventCategories(*packets[3]);
  ASSERT_EQ(event_categories.size(), 1);

  const auto inner_category_iid = event_categories.at("inner");
  ASSERT_GT(inner_category_iid, 0);
  ASSERT_NE(inner_category_iid, outer_category_iid);

  AssertTrackEventHasIid(*packets[3], inner_event1_iid, inner_category_iid);

  AssertIsTrackEventSliceBegin(*packets[4], thread_track_uuid, sequence_id);
  event_names = GetInternedEventNames(*packets[4]);
  ASSERT_EQ(event_names.size(), 1);

  // First InnerInnerEvent1, inner packet
  const auto inner_inner_event1_iid = event_names.at("InnerInnerEvent1");
  ASSERT_GT(inner_inner_event1_iid, 0);
  ASSERT_NE(inner_inner_event1_iid, inner_event1_iid);
  ASSERT_NE(inner_inner_event1_iid, outer_event_iid);

  event_categories = GetInternedEventCategories(*packets[4]);
  ASSERT_EQ(event_categories.size(), 0);

  AssertTrackEventHasIid(*packets[4], inner_inner_event1_iid, inner_category_iid);

  AssertIsTrackEventSliceEnd(*packets[5], thread_track_uuid, sequence_id);
  AssertTrackEventDuration(*packets[4], *packets[5], 1000000, 10000000);

  // First InnerInnerEvent2, inner packet
  AssertIsTrackEventSliceBegin(*packets[6], thread_track_uuid, sequence_id);
  event_names = GetInternedEventNames(*packets[6]);
  ASSERT_EQ(event_names.size(), 1);

  const auto inner_inner_event2_iid = event_names.at("InnerInnerEvent2");
  ASSERT_GT(inner_inner_event2_iid, 0);
  ASSERT_NE(inner_inner_event2_iid, inner_inner_event1_iid);
  ASSERT_NE(inner_inner_event2_iid, inner_event1_iid);
  ASSERT_NE(inner_inner_event2_iid, outer_event_iid);

  AssertTrackEventHasIid(*packets[6], inner_inner_event2_iid, inner_category_iid);

  AssertIsTrackEventSliceEnd(*packets[7], thread_track_uuid, sequence_id);
  AssertTrackEventDuration(*packets[6], *packets[7], 1000000, 10000000);

  AssertIsTrackEventSliceEnd(*packets[8], thread_track_uuid, sequence_id);
  AssertTrackEventDuration(*packets[3], *packets[8], 2000000, 20000000);

  // First InnerEvent2, inner packet
  AssertIsTrackEventSliceBegin(*packets[9], thread_track_uuid, sequence_id);

  event_names = GetInternedEventNames(*packets[9]);
  ASSERT_EQ(event_names.size(), 1);

  const auto inner_event2_iid = event_names.at("InnerEvent2");
  ASSERT_GT(inner_event2_iid, 0);
  ASSERT_NE(inner_event2_iid, inner_inner_event2_iid);
  ASSERT_NE(inner_event2_iid, inner_inner_event1_iid);
  ASSERT_NE(inner_event2_iid, inner_event1_iid);
  ASSERT_NE(inner_event2_iid, outer_event_iid);

  AssertTrackEventHasIid(*packets[9], inner_event2_iid, inner_category_iid);

  AssertIsTrackEventSliceEnd(*packets[10], thread_track_uuid, sequence_id);
  AssertTrackEventDuration(*packets[9], *packets[10], 2000000, 20000000);

  AssertIsTrackEventSliceEnd(*packets[11], thread_track_uuid, sequence_id);
  AssertTrackEventDuration(*packets[2], *packets[11], 4000000, 20000000);
}

TEST_F(SingleThreadTracingTest, InstantEvent) {
  regular_thread_->RunOneIteration([](MockRegularThread* self) {
    self->TracerForTest().InstantEvent("MyCoolEvent", "instant");
  });

  app_.StopTraceSession();

  auto traces = sink_->LoggedTraces();
  auto packets = GetPacketsFromTraces(traces);
  ASSERT_EQ(packets.size(), 3);

  AssertIsProcessTrackDescriptor(*packets[0], kAppName);
  const auto process_track_uuid = packets[0]->track_descriptor().uuid();

  AssertIsThreadTrackDescriptor(*packets[1], kRegularThreadName, process_track_uuid);
  auto thread_track_uuid = packets[1]->track_descriptor().uuid();

  AssertIsTrackEventInstant(*packets[2], thread_track_uuid);

  const auto event_names = GetInternedEventNames(*packets[2]);
  ASSERT_EQ(event_names.size(), 1);

  const auto event_name_iid = event_names.at("MyCoolEvent");
  ASSERT_GT(event_name_iid, 0);

  const auto event_categories = GetInternedEventCategories(*packets[2]);
  ASSERT_EQ(event_categories.size(), 1);

  const auto category_iid = event_categories.at("instant");
  ASSERT_GT(category_iid, 0);

  AssertTrackEventHasIid(*packets[2], event_name_iid, category_iid);
}

TEST_F(SingleThreadTracingTest, StopTracingAndNoEventsAreRecorded) {
  app_.StopTraceSession();

  regular_thread_->RunOneIteration([](MockRegularThread* self) {
    self->TracerForTest().InstantEvent("MyCoolEvent", "instant");
  });

  auto traces = sink_->LoggedTraces();
  auto packets = GetPacketsFromTraces(traces);
  ASSERT_EQ(packets.size(), 2);

  AssertIsProcessTrackDescriptor(*packets[0], kAppName);
  const auto process_track_uuid = packets[0]->track_descriptor().uuid();

  AssertIsThreadTrackDescriptor(*packets[1], kRegularThreadName, process_track_uuid);
}

TEST_F(SingleThreadTracingTest, RestartTracingStartsNewSession) {
  regular_thread_->RunOneIteration([](MockRegularThread* self) {
    auto span = self->TracerForTest().WithSpan("Event1");
    WasteTime(std::chrono::microseconds(1000));
  });

  app_.StopTraceSession();

  auto traces = sink_->LoggedTraces();
  auto packets = GetPacketsFromTraces(traces);
  ASSERT_EQ(packets.size(), 4);

  auto event1_thread_sequence_id1 = packets[2]->trusted_packet_sequence_id();

  regular_thread_->RunOneIteration([](MockRegularThread* self) {
    auto span = self->TracerForTest().WithSpan("Event2");
    WasteTime(std::chrono::microseconds(1000));
  });

  sink_->Clear();  // clear the sink so we have a fresh start when restarting trace
  app_.StartTraceSession(sink_);

  regular_thread_->RunOneIteration([](MockRegularThread* self) {
    {
      auto span = self->TracerForTest().WithSpan("Event3");
      WasteTime(std::chrono::microseconds(1000));
    }

    {
      auto span = self->TracerForTest().WithSpan("Event1");
      WasteTime(std::chrono::microseconds(1000));
    }
  });

  app_.StopTraceSession();

  auto traces2 = sink_->LoggedTraces();
  auto packets2 = GetPacketsFromTraces(traces2);
  ASSERT_EQ(packets2.size(), 6);

  AssertIsProcessTrackDescriptor(*packets2[0], kAppName);
  const auto process_track_uuid = packets2[0]->track_descriptor().uuid();

  AssertIsThreadTrackDescriptor(*packets2[1], kRegularThreadName, process_track_uuid);
  auto thread_track_uuid = packets2[1]->track_descriptor().uuid();

  AssertIsTrackEventSliceBegin(*packets2[2], thread_track_uuid);

  // Since we started a new trace session, the interned data is reset. So the first event is only expected to have Event3 on it.
  // Note Event2 is lost as designed
  auto event_names = GetInternedEventNames(*packets2[2]);
  ASSERT_EQ(event_names.size(), 1);

  auto event3_name_iid = event_names.at("Event3");
  ASSERT_GT(event3_name_iid, 0);

  auto sequence_id = packets2[2]->trusted_packet_sequence_id();

  ASSERT_EQ(event1_thread_sequence_id1, sequence_id);

  AssertTrackEventHasIid(*packets2[2], event3_name_iid, 0);

  AssertIsTrackEventSliceEnd(*packets2[3], thread_track_uuid, sequence_id);

  AssertTrackEventDuration(*packets2[2], *packets2[3], 1000000, 10000000);

  // Now let's check if Event1 will be properly written out again.

  AssertIsTrackEventSliceBegin(*packets2[4], thread_track_uuid);

  event_names = GetInternedEventNames(*packets2[4]);
  ASSERT_EQ(event_names.size(), 1);

  auto event1_name_iid = event_names.at("Event1");
  ASSERT_GT(event1_name_iid, 0);

  AssertTrackEventHasIid(*packets2[4], event1_name_iid, 0);

  AssertIsTrackEventSliceEnd(*packets2[5], thread_track_uuid, sequence_id);

  AssertTrackEventDuration(*packets2[4], *packets2[5], 1000000, 10000000);
}

TEST_F(SingleThreadTracingTest, QueueOverflowWillNotBlock) {
  // To make the queue overflow, we intentionally stop the TraceAggregator
  app_.StopTraceAggregator();

  // Fill the queue
  regular_thread_->RunOneIteration([](MockRegularThread* self) {
    for (size_t i = 0; i < self->TracerForTest().QueueCapacity(); ++i) {
      self->TracerForTest().InstantEvent("Event");
    }
  });

  // Test it doesn't block
  regular_thread_->RunOneIteration([](MockRegularThread* self) {
    for (int i = 0; i < 5; ++i) {
      self->TracerForTest().InstantEvent("Event");
    }
  });
}

TEST_F(SingleThreadTracingTest, TraceAggregatorCPUAffinity) {
  GTEST_SKIP() << "TODO";
}

TEST_F(SingleThreadTracingTest, CorrectlyHandleSinkWriterFailure) {
  GTEST_SKIP() << "TODO";
}

}  // namespace cactus_rt
