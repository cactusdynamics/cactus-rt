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

class RTROS2PublisherThread : public cactus_rt::CyclicThread, public cactus_rt::ros2::Ros2ThreadMixin {
  int64_t last_published_at_ = 0;
  int64_t run_duration_;

  std::shared_ptr<cactus_rt::ros2::Publisher<RealtimeType, RosType>> publisher_;

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
    publisher_ = ros2_adapter.CreatePublisher<RealtimeType, RosType>("/cactus_rt/complex", rclcpp::QoS(100));
  }

 protected:
  LoopControl Loop(int64_t elapsed_ns) noexcept override {
    if (elapsed_ns - last_published_at_ > 10'000'000) {
      last_published_at_ = elapsed_ns;

      const auto span = Tracer().WithSpan("Publish");

      const auto elapsed_ns_f = static_cast<float>(elapsed_ns);

      const MyCoefficientData msg{
        elapsed_ns_f,
        elapsed_ns_f / 10.0F,
        elapsed_ns_f / 100.0F,
        elapsed_ns_f / 1000.0F
      };

      const auto success = publisher_->Publish(msg);
      LOG_INFO(
        Logger(),
        "{} data {}, {}, {}, {}",
        success ? "Published" : "Did not publish",
        msg.a,
        msg.b,
        msg.c,
        msg.d
      );
    }

    return elapsed_ns > run_duration_ ? LoopControl::Stop : LoopControl::Continue;
  }
};

int main(int argc, const char* argv[]) {
  const cactus_rt::AppConfig app_config;

  cactus_rt::ros2::Ros2Adapter::Config ros2_adapter_config;
  ros2_adapter_config.timer_interval = std::chrono::milliseconds(50);

  cactus_rt::ros2::App app(argc, argv, "ComplexDataROS2Publisher", app_config, ros2_adapter_config);
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
