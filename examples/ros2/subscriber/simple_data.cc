#include <cactus_rt/ros2/app.h>
#include <cactus_rt/rt.h>

#include <chrono>
#include <memory>
#include <std_msgs/msg/int64.hpp>

using RealtimeType = std_msgs::msg::Int64;
using RosType = std_msgs::msg::Int64;

class RTROS2SubscriberThread : public cactus_rt::CyclicThread, public cactus_rt::ros2::Ros2ThreadMixin {
  int64_t last_msg_id_ = 0;
  int64_t run_duration_;

  // We force turn off the trivial data check, because the ROS message data type
  // has a defined constructor with code in it. That said, the code really is
  // pretty trivial so it is safe to use in real-time. We thus disable the trivial
  // type check manually.
  std::shared_ptr<cactus_rt::ros2::SubscriptionLatest<RealtimeType, RosType, false>> subscription_;

  static cactus_rt::CyclicThreadConfig MakeConfig() {
    cactus_rt::CyclicThreadConfig thread_config;
    thread_config.period_ns = 1'000'000;
    thread_config.cpu_affinity = std::vector<size_t>{2};
    thread_config.SetFifoScheduler(80);

    return thread_config;
  }

 public:
  explicit RTROS2SubscriberThread(std::chrono::nanoseconds run_duration = std::chrono::seconds(30))
      : cactus_rt::CyclicThread("RTROS2Subscriber", MakeConfig()),
        run_duration_(run_duration.count()) {}

  void InitializeForRos2(cactus_rt::ros2::Ros2Adapter& ros2_adapter) override {
    subscription_ = ros2_adapter.CreateSubscriptionForLatestValue<RealtimeType, RosType, false>("/cactus_rt/simple", rclcpp::QoS(100));
  }

 protected:
  LoopControl Loop(int64_t elapsed_ns) noexcept override {
    cactus_rt::ros2::StampedValue<std_msgs::msg::Int64> msg;
    {
      const auto span = Tracer().WithSpan("Subscription::ReadLatest");
      msg = subscription_->ReadLatest();
    }

    if (msg.id != last_msg_id_) {
      LOG_INFO(Logger(), "Got new data at {}: {} {}", elapsed_ns, msg.id, msg.value.data);
      last_msg_id_ = msg.id;
    }

    return elapsed_ns > run_duration_ ? LoopControl::Stop : LoopControl::Continue;
  }
};

int main(int argc, const char* argv[]) {
  cactus_rt::ros2::App app(argc, argv, "SimpleDataROS2Subscriber");
  app.StartTraceSession("build/subscriber.perfetto");

  constexpr std::chrono::seconds time(30);
  std::cout << "Testing RT loop for " << time.count() << " seconds.\n";

  auto thread = app.CreateROS2EnabledThread<RTROS2SubscriberThread>(time);

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
