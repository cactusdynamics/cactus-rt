#include <cactus_rt/ros2/app.h>
#include <cactus_rt/rt.h>

#include <chrono>
#include <memory>
#include <std_msgs/msg/int64.hpp>

using RealtimeType = std_msgs::msg::Int64;
using RosType = std_msgs::msg::Int64;

class RTROS2PublisherThread : public cactus_rt::CyclicThread, public cactus_rt::ros2::Ros2ThreadMixin {
  int64_t last_published_at_ = 0;
  int64_t run_duration_;

  // We force turn off the trivial data check, because the ROS message data type
  // has a defined constructor with code in it. That said, the code really is
  // pretty trivial so it is safe to use in real-time. We thus disable the trivial
  // type check manually.
  std::shared_ptr<cactus_rt::ros2::Publisher<RealtimeType, RosType, false>> publisher_;

  static cactus_rt::CyclicThreadConfig MakeConfig() {
    cactus_rt::CyclicThreadConfig thread_config;
    thread_config.period_ns = 1'000'000;
    thread_config.cpu_affinity = std::vector<size_t>{2};
    thread_config.SetFifoScheduler(80);

    return thread_config;
  }

 public:
  explicit RTROS2PublisherThread(std::chrono::nanoseconds run_duration = std::chrono::seconds(30))
      : cactus_rt::CyclicThread("RTROS2Publisher", MakeConfig()),
        run_duration_(run_duration.count()) {}

  void InitializeForRos2(cactus_rt::ros2::Ros2Adapter& ros2_adapter) override {
    publisher_ = ros2_adapter.CreatePublisher<RealtimeType, RosType, false>("/cactus_rt/simple", rclcpp::QoS(100));
  }

 protected:
  LoopControl Loop(int64_t elapsed_ns) noexcept override {
    if (elapsed_ns - last_published_at_ > 10'000'000) {
      last_published_at_ = elapsed_ns;

      const auto span = Tracer().WithSpan("Publish");

      std_msgs::msg::Int64 msg;
      msg.data = elapsed_ns;
      const auto success = publisher_->Publish(msg);
      LOG_INFO(Logger(), "{} integer {}", success ? "Published" : "Did not publish", msg.data);
    }

    return elapsed_ns > run_duration_ ? LoopControl::Stop : LoopControl::Continue;
  }
};

int main(int argc, const char* argv[]) {
  const cactus_rt::AppConfig app_config;

  cactus_rt::ros2::Ros2Adapter::Config ros2_adapter_config;
  ros2_adapter_config.timer_interval = std::chrono::milliseconds(50);

  cactus_rt::ros2::App app(argc, argv, "SimpleDataROS2Publisher", app_config, ros2_adapter_config);
  app.StartTraceSession("build/publisher.perfetto");

  constexpr std::chrono::seconds time(30);
  std::cout << "Testing RT loop for " << time.count() << " seconds.\n";

  auto thread = app.CreateROS2EnabledThread<RTROS2PublisherThread>(time);

  app.Start();

  std::thread t([&app, &time]() {
    std::this_thread::sleep_for(time);
    app.RequestStop();
  });
  t.detach();

  app.Join();

  std::cout << "Done\n";
  return 0;
}
