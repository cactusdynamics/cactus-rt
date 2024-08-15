#include <gtest/gtest.h>

#include <memory>
#include <rclcpp/rclcpp.hpp>
#include <std_msgs/msg/float32_multi_array.hpp>
#include <std_msgs/msg/int64.hpp>

#include "ping_pong_ros_thread.h"

class TestPingPong : public ::testing::Test {
 protected:
  std::shared_ptr<rclcpp::Node>                                     node_;
  rclcpp::Subscription<std_msgs::msg::Int64>::SharedPtr             simple_sub_;
  rclcpp::Subscription<std_msgs::msg::Float32MultiArray>::SharedPtr complex_sub_;
  rclcpp::Publisher<std_msgs::msg::Int64>::SharedPtr                simple_pub_;
  rclcpp::Publisher<std_msgs::msg::Float32MultiArray>::SharedPtr    complex_pub_;

  std::unique_ptr<rclcpp::executors::SingleThreadedExecutor> executor_;
  std::thread                                                executor_thread_;

  std::mutex                       mut_;
  std_msgs::msg::Int64             simple_sub_msg_;
  std_msgs::msg::Float32MultiArray complex_sub_msg_;

  std::thread ros_thread_;
  pid_t       child_process_;

  void SetUp() override {
    // Fork first, then run ROS stuff later.
    child_process_ = StartPingPongRosProcess();

    const char* argv[] = {"cactus_rt_ros2_test"};  // NOLINT
    rclcpp::init(1, argv);

    node_ = std::make_shared<rclcpp::Node>("test_node");

    simple_sub_ = node_->create_subscription<std_msgs::msg::Int64>(
      "/cactus_rt/test/simple_pub",  // This side we create a subscription for the publisher of the cactus_rt::ros2:App
      10,
      [this](const std_msgs::msg::Int64& msg) {
        const std::scoped_lock lock(mut_);
        simple_sub_msg_ = msg;
      }
    );

    complex_sub_ = node_->create_subscription<std_msgs::msg::Float32MultiArray>(
      "/cactus_rt/test/complex_pub",
      10,
      [this](const std_msgs::msg::Float32MultiArray& msg) {
        const std::scoped_lock lock(mut_);
        complex_sub_msg_ = msg;
      }
    );

    simple_pub_ = node_->create_publisher<std_msgs::msg::Int64>("/cactus_rt/tests/simple_sub", 10);
    complex_pub_ = node_->create_publisher<std_msgs::msg::Float32MultiArray>("/cactus_rt/tests/complex_sub", 10);

    ros_thread_ = std::thread([this]() {
      rclcpp::spin(node_);
    });
  }

  void TearDown() override {
    if (child_process_ != 0) {
      ForceStopProcess(child_process_);
      child_process_ = 0;
    }
    rclcpp::shutdown();
    ros_thread_.join();
  }
};

TEST_F(TestPingPong, PingPong) {
  auto start = cactus_rt::NowNs();
  bool got_data = false;
  while (cactus_rt::NowNs() - start < 1'000'000'000) {
    const std::scoped_lock lock(mut_);
    if (simple_sub_msg_.data == 1337) {
      got_data = true;
      break;
    }

    std::this_thread::sleep_for(std::chrono::milliseconds(3));
  }

  ASSERT_TRUE(got_data);

  std_msgs::msg::Int64 msg1;
  msg1.data = 1234;
  simple_pub_->publish(msg1);

  got_data = false;
  while (cactus_rt::NowNs() - start < 1'000'000'000) {
    const std::scoped_lock lock(mut_);
    if (simple_sub_msg_.data == 1234) {
      got_data = true;
      break;
    }

    std::this_thread::sleep_for(std::chrono::milliseconds(3));
  }

  ASSERT_TRUE(got_data);
}

int main(int argc, char** argv) {
  testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
