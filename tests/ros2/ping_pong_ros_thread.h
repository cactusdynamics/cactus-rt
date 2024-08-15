#ifndef CACTUS_RT_TESTS_ROS2_TEST_ROS2_THREADS_H_
#define CACTUS_RT_TESTS_ROS2_TEST_ROS2_THREADS_H_

#include <cactus_rt/ros2/app.h>
#include <cactus_rt/ros2/publisher.h>
#include <cactus_rt/ros2/subscription.h>
#include <cactus_rt/rt.h>
#include <unistd.h>

#include <memory>
#include <std_msgs/msg/float32_multi_array.hpp>
#include <std_msgs/msg/int64.hpp>

struct RealtimeTestData {
  float a;
  float b;
  float c;
};

template <>
struct rclcpp::TypeAdapter<RealtimeTestData, std_msgs::msg::Float32MultiArray> {
  using is_specialized = std::true_type;
  using custom_type = RealtimeTestData;
  using ros_message_type = std_msgs::msg::Float32MultiArray;

  static void convert_to_ros_message(const custom_type& source, ros_message_type& destination);
  static void convert_to_custom(const ros_message_type& source, custom_type& destination);
};

class PingPongRosThread : public cactus_rt::Thread, public cactus_rt::ros2::Ros2ThreadMixin {
  static cactus_rt::ThreadConfig MakeConfig();

  using SimpleDataPublisher = cactus_rt::ros2::Publisher<std_msgs::msg::Int64, std_msgs::msg::Int64, false>;
  std::shared_ptr<SimpleDataPublisher> simple_data_publisher_;

  using ComplexDataPublisher = cactus_rt::ros2::Publisher<RealtimeTestData, std_msgs::msg::Float32MultiArray>;
  std::shared_ptr<ComplexDataPublisher> complex_data_publisher_;

  using SimpleDataSubscriberLatest = cactus_rt::ros2::SubscriptionLatest<std_msgs::msg::Int64, std_msgs::msg::Int64, false>;
  std::shared_ptr<SimpleDataSubscriberLatest> simple_data_subscriber_;

  using ComplexDataSubscriberLatest = cactus_rt::ros2::SubscriptionLatest<RealtimeTestData, std_msgs::msg::Float32MultiArray>;
  std::shared_ptr<ComplexDataSubscriberLatest> complex_data_subscriber_;

 public:
  PingPongRosThread();
  void InitializeForRos2() override;

 protected:
  void Run() override;

 private:
  template <typename T>
  std::optional<T> WaitForMessage(std::chrono::nanoseconds timeout, std::function<std::optional<T>()> get_msg) {
    const auto timeout_ns = timeout.count();
    const auto start = cactus_rt::NowNs();

    while (cactus_rt::NowNs() - start < timeout_ns) {
      std::optional<T> msg = get_msg();
      if (msg) {
        return msg;
      }

      std::this_thread::sleep_for(std::chrono::milliseconds(10));
    }

    return std::nullopt;
  }
};

// The child process will not return from this until the end of the program.
// The parent process will return from this.
pid_t StartPingPongRosProcess();

void ForceStopProcess(pid_t pid);

#endif
