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
        regular_thread_(std::make_shared<MockRegularThread>()),
        sink_(std::make_shared<MockSink>()) {}

 protected:
  void SetUp() override {
    app_.RegisterThread(regular_thread_);
    app_.StartTraceSession();  // TODO: make each test manually start the trace session!

    app_.RegisterTraceSink(sink_);

    app_.Start();
  }

  void TearDown() override {
    app_.RequestStop();
    app_.Join();

    // Need to stop it for every test as every app.Start() will start a background thread.
    quill::detail::LogManagerSingleton::instance().log_manager().stop_backend_worker();
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
  AssertIsTrackEventSliceBegin(*packets[2], "TestEvent", "category", thread_track_uuid);
  auto sequence_id = packets[2]->trusted_packet_sequence_id();

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

  AssertIsTrackEventSliceBegin(*packets[2], "OuterEvent", "outer", thread_track_uuid);
  auto sequence_id = packets[2]->trusted_packet_sequence_id();

  AssertIsTrackEventSliceBegin(*packets[3], "InnerEvent1", "inner", thread_track_uuid, sequence_id);

  AssertIsTrackEventSliceBegin(*packets[4], "InnerInnerEvent1", "inner", thread_track_uuid, sequence_id);
  AssertIsTrackEventSliceEnd(*packets[5], thread_track_uuid, sequence_id);
  AssertTrackEventDuration(*packets[4], *packets[5], 1000000, 10000000);

  AssertIsTrackEventSliceBegin(*packets[6], "InnerInnerEvent2", "inner", thread_track_uuid, sequence_id);
  AssertIsTrackEventSliceEnd(*packets[7], thread_track_uuid, sequence_id);
  AssertTrackEventDuration(*packets[6], *packets[7], 1000000, 10000000);

  AssertIsTrackEventSliceEnd(*packets[8], thread_track_uuid, sequence_id);
  AssertTrackEventDuration(*packets[3], *packets[8], 2000000, 20000000);

  AssertIsTrackEventSliceBegin(*packets[9], "InnerEvent2", "inner", thread_track_uuid, sequence_id);
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

  AssertIsTrackEventInstant(*packets[2], "MyCoolEvent", "instant", thread_track_uuid);
}

TEST_F(SingleThreadTracingTest, StopTracingAndNoEventsAreRecorded) {
  app_.StopTraceSession();

  regular_thread_->RunOneIteration([](MockRegularThread* self) {
    self->TracerForTest().InstantEvent("MyCoolEvent", "instant");
  });

  auto traces = sink_->LoggedTraces();
  auto packets = GetPacketsFromTraces(traces);
  ASSERT_EQ(packets.size(), 1);

  AssertIsProcessTrackDescriptor(*packets[0], kAppName);
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

  regular_thread_->RunOneIteration([](MockRegularThread* self) {
    auto span = self->TracerForTest().WithSpan("Event2");
    WasteTime(std::chrono::microseconds(1000));
  });

  // In normal API usage, we always have to re-register sinks after starting a
  // trace session, which may not be ideal?? Alternatively could use the short
  // hand API to log directly to file...
  app_.StartTraceSession();
  sink_->Clear();                 // clear the sink so we have a fresh start when restarting trace
  app_.RegisterTraceSink(sink_);  // TODO: make it so that sinks are cached???? Doesn't make sense tho.

  regular_thread_->RunOneIteration([](MockRegularThread* self) {
    auto span = self->TracerForTest().WithSpan("Event3");
    WasteTime(std::chrono::microseconds(1000));
  });

  app_.StopTraceSession();

  auto traces2 = sink_->LoggedTraces();
  auto packets2 = GetPacketsFromTraces(traces2);
  ASSERT_EQ(packets2.size(), 4);

  AssertIsProcessTrackDescriptor(*packets2[0], kAppName);
  const auto process_track_uuid = packets2[0]->track_descriptor().uuid();

  AssertIsThreadTrackDescriptor(*packets2[1], kRegularThreadName, process_track_uuid);
  auto thread_track_uuid = packets2[1]->track_descriptor().uuid();

  // Note Event2 is lost as designed
  AssertIsTrackEventSliceBegin(*packets2[2], "Event3", nullptr, thread_track_uuid);
  auto sequence_id = packets2[2]->trusted_packet_sequence_id();

  AssertIsTrackEventSliceEnd(*packets2[3], thread_track_uuid, sequence_id);

  AssertTrackEventDuration(*packets2[2], *packets2[3], 1000000, 10000000);
}

TEST_F(SingleThreadTracingTest, DynamicallyAddingSinkWillWork) {
  regular_thread_->RunOneIteration([](MockRegularThread* self) {
    const auto span = self->TracerForTest().WithSpan("Event1");
    WasteTime(std::chrono::microseconds(1000));
  });

  // This is kind of a hack to ensure the data from the previous only made it to
  // sink_. If we don't wait for a bit, there's a race condition where sink2
  // could get these data.
  // Unfortunately this has to be implemented via a sleep. This is not idea but
  // it is the best option for now.
  std::this_thread::sleep_for(std::chrono::milliseconds(200));

  auto sink2 = std::make_shared<MockSink>();
  app_.RegisterTraceSink(sink2);

  regular_thread_->RunOneIteration([](MockRegularThread* self) {
    self->TracerForTest().InstantEvent("Event2");
  });

  app_.StopTraceSession();
  auto traces2 = sink2->LoggedTraces();
  auto packets2 = GetPacketsFromTraces(traces2);

  ASSERT_EQ(packets2.size(), 3);

  AssertIsProcessTrackDescriptor(*packets2[0], kAppName);
  const auto process_track_uuid = packets2[0]->track_descriptor().uuid();

  AssertIsThreadTrackDescriptor(*packets2[1], kRegularThreadName, process_track_uuid);
  auto thread_track_uuid = packets2[1]->track_descriptor().uuid();

  AssertIsTrackEventInstant(*packets2[2], "Event2", nullptr, thread_track_uuid);

  auto traces = sink_->LoggedTraces();
  auto packets = GetPacketsFromTraces(traces);

  ASSERT_EQ(packets.size(), 5);
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
