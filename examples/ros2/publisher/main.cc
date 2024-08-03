#include <cactus_rt/ros2/app.h>
#include <cactus_rt/rt.h>

#include <chrono>
#include <iostream>
#include <memory>
#include <std_msgs/msg/int64.hpp>
#include <thread>

using cactus_rt::CyclicThread;
using cactus_rt::ros2::App;

struct RealtimeData {
  int64_t data;

  RealtimeData() = default;
  explicit RealtimeData(int64_t d) : data(d) {}
};
using RosData = std_msgs::msg::Int64;

namespace {
void RealtimeToROS2ConverterFunc(const RealtimeData& rt_data, RosData& ros_data) {
  // A bit of a silly example, but gets the point across.
  ros_data.data = rt_data.data;
}
}  // namespace

class RealtimeROS2PublisherThread : public CyclicThread, public cactus_rt::ros2::Ros2ThreadMixin {
  int64_t                                                            loop_counter_ = 0;
  std::shared_ptr<cactus_rt::ros2::Publisher<RealtimeData, RosData>> publisher_;

  static cactus_rt::CyclicThreadConfig CreateThreadConfig() {
    cactus_rt::CyclicThreadConfig thread_config;
    thread_config.period_ns = 1'000'000;
    thread_config.cpu_affinity = std::vector<size_t>{2};
    thread_config.SetFifoScheduler(80);

    // thread_config.tracer_config.trace_sleep = true;
    thread_config.tracer_config.trace_wakeup_latency = true;
    return thread_config;
  }

 public:
  RealtimeROS2PublisherThread(const char* name) : CyclicThread(name, CreateThreadConfig()) {}

  void InitializeForRos2() override {
    publisher_ = ros2_adapter_->CreatePublisher<RealtimeData, RosData>("/hello", rclcpp::QoS(10), RealtimeToROS2ConverterFunc);
  }

  int64_t GetLoopCounter() const {
    return loop_counter_;
  }

 protected:
  bool Loop(int64_t /*now*/) noexcept final {
    loop_counter_++;
    if (loop_counter_ % 1000 == 0) {
      LOG_INFO(Logger(), "Loop {}", loop_counter_);

      const auto span = Tracer().WithSpan("Publish");
      publisher_->Publish(loop_counter_);
    }
    return false;
  }
};

int main(int argc, char* argv[]) {
  rclcpp::init(argc, argv);

  App app;
  app.StartTraceSession("build/data.perfetto");

  auto thread = app.CreateROS2EnabledThread<RealtimeROS2PublisherThread>("RTROS2PublisherThread");
  app.RegisterThread(thread);

  constexpr unsigned int time = 30;
  std::cout << "Testing RT loop for " << time << " seconds.\n";

  app.Start();

  std::this_thread::sleep_for(std::chrono::seconds(time));

  app.RequestStop();
  app.Join();

  std::cout << "Number of loops executed: " << thread->GetLoopCounter() << "\n";
  return 0;
}
