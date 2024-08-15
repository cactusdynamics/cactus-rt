#include "ping_pong_ros_thread.h"

#include <sys/wait.h>

#include <csignal>

using namespace std::literals::chrono_literals;

void rclcpp::TypeAdapter<RealtimeTestData, std_msgs::msg::Float32MultiArray>::convert_to_custom(const ros_message_type& source, custom_type& destination) {
  assert(source.data.size() == 3);
  destination.a = source.data[0];
  destination.b = source.data[1];
  destination.c = source.data[2];
}

void rclcpp::TypeAdapter<RealtimeTestData, std_msgs::msg::Float32MultiArray>::convert_to_ros_message(const custom_type& source, ros_message_type& destination) {
  destination.data.reserve(3);
  destination.data[0] = source.a;
  destination.data[1] = source.b;
  destination.data[2] = source.c;
}

cactus_rt::ThreadConfig PingPongRosThread::MakeConfig() {
  cactus_rt::ThreadConfig config;
  config.SetOtherScheduler(0);
  return config;
}

PingPongRosThread::PingPongRosThread()
    : cactus_rt::Thread("PingPongRosThread", MakeConfig()) {}

void PingPongRosThread::InitializeForRos2() {
  simple_data_publisher_ = ros2_adapter_->CreatePublisher<std_msgs::msg::Int64, std_msgs::msg::Int64, false>(
    "/cactus_rt/test/simple_pub",
    rclcpp::QoS(10)
  );

  simple_data_subscriber_ = ros2_adapter_->CreateSubscriptionForLatestValue<std_msgs::msg::Int64, std_msgs::msg::Int64, false>(
    "/cactus_rt/test/simple_sub",
    rclcpp::QoS(10)
  );

  complex_data_publisher_ = ros2_adapter_->CreatePublisher<RealtimeTestData, std_msgs::msg::Float32MultiArray>(
    "/cactus_rt/test/complex_pub",
    rclcpp::QoS(10)
  );

  complex_data_subscriber_ = ros2_adapter_->CreateSubscriptionForLatestValue<RealtimeTestData, std_msgs::msg::Float32MultiArray>(
    "/cactus_rt/test/complex_sub",
    rclcpp::QoS(10)
  );
}

void PingPongRosThread::Run() {
  // A few things are supposed to happen:
  // 1. Send a message to indicate that this thread has started.
  //    This also tests that we are publishing the data correctly without
  //    conversion.
  std_msgs::msg::Int64 initial_msg;
  initial_msg.data = 1337;
  LOG_DEBUG(Logger(), "Publishing initial message");
  simple_data_publisher_->Publish(initial_msg);

  // 2. Wait for a simple message from the test thread. This also test that we
  //    can receive a message without conversion.
  LOG_DEBUG(Logger(), "Waiting for first message");
  auto msg1 = WaitForMessage<cactus_rt::ros2::StampedValue<std_msgs::msg::Int64>>(
    std::chrono::milliseconds(1000), [this]() -> std::optional<cactus_rt::ros2::StampedValue<std_msgs::msg::Int64>> {
      auto msg = simple_data_subscriber_->ReadLatest();
      std::cerr << "First message " << msg.id << "\n";
      if (msg.id == 1) {
        return std::make_optional(msg);
      }

      if (msg.id > 1) {
        throw std::runtime_error("simple msg id greater than 1");
      }

      return std::nullopt;
    }
  );

  LOG_DEBUG(Logger(), "Got first message");
  if (!msg1.has_value()) {
    throw std::runtime_error("timed out waiting for first message");
  }

  if (msg1->value.data != 42) {
    std::cerr << "didn't get 42 but got " << msg1->value.data << "\n";
  }

  // 3. Send the same simple message back to the test thread.
  std_msgs::msg::Int64 response_msg1;
  response_msg1.data = msg1->value.data;
  LOG_DEBUG(Logger(), "Publishing second message");
  simple_data_publisher_->Publish(response_msg1);

  // 4. Wait for a complex message from the test thread.
  LOG_DEBUG(Logger(), "Waiting for third message");
  auto msg2 = WaitForMessage<cactus_rt::ros2::StampedValue<RealtimeTestData>>(
    std::chrono::milliseconds(1000),
    [this]() -> std::optional<cactus_rt::ros2::StampedValue<RealtimeTestData>> {
      auto msg = complex_data_subscriber_->ReadLatest();

      if (msg.id == 1) {
        return std::make_optional(msg);
      }

      if (msg.id > 1) {
        throw std::runtime_error("complex msg id greater than 1");
      }

      return std::nullopt;
    }
  );

  if (!msg2.has_value()) {
    throw std::runtime_error("timed out waiting for second message");
  }

  // 5. Send the same complex message back to the test thrad.
  RealtimeTestData response_msg2;
  response_msg2.a = msg2->value.a;
  response_msg2.b = msg2->value.b;
  response_msg2.c = msg2->value.c;
  LOG_DEBUG(Logger(), "Publishing fourth message");
  complex_data_publisher_->Publish(response_msg2);
  LOG_DEBUG(Logger(), "Done");
}

int PingPongAppMain() {
  const char* argv[] = {"ping_pong_test_app"};  // NOLINT

  cactus_rt::ros2::App app(1, argv, "PingPongTestApp");

  auto thread = app.CreateROS2EnabledThread<PingPongRosThread>();
  app.RegisterThread(thread);

  app.Start();
  app.Join();

  return 0;
}

pid_t StartPingPongRosProcess() {
  // When the child process quits, a SIGCHLD is sent to the parent. We ignore it.
  if (signal(SIGCHLD, SIG_IGN) == SIG_ERR) {
    throw std::runtime_error(std::string("cannot setup signal handler: ") + std::strerror(errno));
  }

  std::cerr << "Forking Ping Pong ROS Process\n";
  pid_t pid = fork();
  if (pid == -1) {
    throw std::runtime_error(std::string("failed to fork: ") + std::strerror(errno));
  }

  if (pid != 0) {
    // This branch is executed by the parent process
    while (true) {
      auto ret = kill(pid, 0);
      if (ret != 0) {
        if (errno == ESRCH) {
          continue;
        }
        throw std::runtime_error(std::string("failed to kill -0: ") + std::strerror(errno));
      }
      break;
    }

    std::cerr << "Ping Pong ROS process started " << pid << "\n";
    return pid;
  }

  std::cerr << "Running Ping Pong App in child process\n";

  // This is executed by the child process.
  exit(PingPongAppMain());
}

void ForceStopProcess(pid_t pid) {
  std::cerr << "Stopping PID " << pid << "\n";
  auto ret = kill(pid, SIGTERM);
  if (ret != 0) {
    if (errno == ESRCH) {
      return;  // Process doesn't exist
    }
    throw std::runtime_error(std::string("failed to kill process: ") + std::strerror(errno));
  }

  std::cerr << "Waiting for PID " << pid << "\n";
  int status = 0;
  ret = waitpid(pid, &status, 0);
  std::cerr << "Status " << status << "\n";
  if (ret == -1) {
    if (errno == ECHILD) {
      return;
    }
    throw std::runtime_error(std::string("failed to waitpid: ") + std::strerror(errno));
  }
}
