#include <cactus_rt/experimental/random.h>
#include <cactus_rt/ros2.h>
#include <cactus_rt/rt.h>

#include <geometry_msgs/msg/twist.hpp>
#include <random>

using namespace std::literals::chrono_literals;
using cactus_rt::experimental::random::RealNumber;
using cactus_rt::ros2::StampedValue;

struct Velocity2D {
  double vx;
  double vy;
  double w;
};

// For demonstration purposes.
void WasteTime(std::chrono::microseconds duration) {
  const auto start = cactus_rt::NowNs();
  auto       duration_ns = duration.count() * 1000;
  while (cactus_rt::NowNs() - start < duration_ns) {
  }
}

template <>
struct rclcpp::TypeAdapter<Velocity2D, geometry_msgs::msg::Twist> {
  using is_specialized = std::true_type;
  using custom_type = Velocity2D;
  using ros_message_type = geometry_msgs::msg::Twist;

  static void convert_to_ros_message(const custom_type& source, ros_message_type& destination) {
    destination.linear.x = source.vx;
    destination.linear.y = source.vy;
    destination.angular.z = source.w;
  }

  static void convert_to_custom(const ros_message_type& source, custom_type& destination) {
    destination.vx = source.linear.x;
    destination.vy = source.linear.y;
    destination.w = source.angular.z;
  }
};

class RT1000 : public cactus_rt::CyclicThread, public cactus_rt::ros2::Ros2ThreadMixin {
  static cactus_rt::CyclicThreadConfig MakeConfig() {
    cactus_rt::CyclicThreadConfig config;
    config.period_ns = 1'000'000;  // 1ms period, 1000 Hz
    config.SetFifoScheduler(80);   // SCHED_FIFO, rtprio = 80
    return config;
  }

  cactus_rt::experimental::random::Xorshift64Rand rand_engine_{std::random_device{}()};

  std::shared_ptr<cactus_rt::ros2::SubscriptionLatest<Velocity2D, geometry_msgs::msg::Twist>> cmd_vel_sub_;
  std::shared_ptr<cactus_rt::ros2::Publisher<Velocity2D, geometry_msgs::msg::Twist>>          feedback_pub_;

 public:
  RT1000() : CyclicThread("RT1000", MakeConfig()) {
    Logger()->set_log_level(quill::LogLevel::Debug);
  }

  void InitializeForRos2(cactus_rt::ros2::Ros2Adapter& ros2_adapter) final {
    cmd_vel_sub_ = ros2_adapter.CreateSubscriptionForLatestValue<Velocity2D, geometry_msgs::msg::Twist>(
      "/cmd_vel", rclcpp::QoS(10)
    );

    feedback_pub_ = ros2_adapter.CreatePublisher<Velocity2D, geometry_msgs::msg::Twist>(
      "/cmd_vel_achieved", rclcpp::QoS(10)
    );
  }

 protected:
  LoopControl Loop(int64_t /*elapsed_ns*/) noexcept final {
    StampedValue<Velocity2D> msg = cmd_vel_sub_->ReadLatest();

    Velocity2D achieved_vel;
    {
      auto span = Tracer().WithSpan("Drive");
      achieved_vel = Drive(msg.value.vx, msg.value.vy, msg.value.w);
    }

    {
      auto span = Tracer().WithSpan("Publish");
      feedback_pub_->Publish(achieved_vel);
    }

    LOG_DEBUG(
      Logger(),
      "Received id = {}; vx, vy, w = {}, {}, {}; Achieved vx, vy, w = {}, {}, {}",
      msg.id,
      msg.value.vx,
      msg.value.vy,
      msg.value.w,
      achieved_vel.vx,
      achieved_vel.vy,
      achieved_vel.w
    );

    return LoopControl::Continue;
  }

 private:
  Velocity2D Drive(double vx, double vy, double w) {
    Velocity2D achieved_vel;
    if (vx != 0.0) {
      achieved_vel.vx = vx + (RealNumber<double>(rand_engine_) - 0.5);
    }

    if (vy != 0.0) {
      achieved_vel.vy = vy + (RealNumber<double>(rand_engine_) - 0.5);
    }

    if (w != 0.0) {
      achieved_vel.w = w + ((RealNumber<double>(rand_engine_) - 0.5) * 0.1);
    }

    // Waste between 100 - 200 us, uniform
    WasteTime(std::chrono::microseconds(static_cast<int64_t>(RealNumber(rand_engine_) * 100.0F + 100.0F)));

    return achieved_vel;
  }
};

int main(int argc, const char* argv[]) {
  cactus_rt::ros2::App app(argc, argv);

  auto thread = app.CreateROS2EnabledThread<RT1000>();

  app.StartTraceSession("build/ros.perfetto");
  app.Start();
  app.Join();

  return 0;
}
