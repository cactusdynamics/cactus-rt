#include <cactus_rt/ros2/app.h>
#include <cactus_rt/rt.h>

#include <chrono>
#include <memory>
#include <std_msgs/msg/float32_multi_array.hpp>

struct MyCoefficientData {
  float a;
  float b;
  float c;
  float d;
};

using RealtimeType = MyCoefficientData;
using RosType = std_msgs::msg::Float32MultiArray;

template <>
struct rclcpp::TypeAdapter<RealtimeType, RosType> {
  using is_specialized = std::true_type;
  using custom_type = RealtimeType;
  using ros_message_type = RosType;

  static void convert_to_ros_message(const custom_type& source, ros_message_type& destination) {
    destination.data.reserve(4);
    destination.data.push_back(source.a);
    destination.data.push_back(source.b);
    destination.data.push_back(source.c);
    destination.data.push_back(source.d);
  }

  static void convert_to_custom(const ros_message_type& source, custom_type& destination) {
    destination.a = source.data.at(0);
    destination.b = source.data.at(1);
    destination.c = source.data.at(2);
    destination.d = source.data.at(3);
  }
};

class RTROS2SubscriberThread : public cactus_rt::CyclicThread, public cactus_rt::ros2::Ros2ThreadMixin {
  int64_t last_msg_id_ = 0;
  int64_t run_duration_;

  std::shared_ptr<cactus_rt::ros2::SubscriptionLatest<RealtimeType, RosType>> subscription_;

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
    subscription_ = ros2_adapter.CreateSubscriptionForLatestValue<RealtimeType, RosType>("/cactus_rt/complex", rclcpp::QoS(100));
  }

 protected:
  LoopControl Loop(int64_t elapsed_ns) noexcept override {
    cactus_rt::ros2::StampedValue<MyCoefficientData> msg;
    {
      const auto span = Tracer().WithSpan("Subscription::ReadLatest");
      msg = subscription_->ReadLatest();
    }

    if (msg.id != last_msg_id_) {
      LOG_INFO(Logger(), "Got new data at {}: {} [{}, {}, {}, {}]", elapsed_ns, msg.id, msg.value.a, msg.value.b, msg.value.c, msg.value.d);
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
