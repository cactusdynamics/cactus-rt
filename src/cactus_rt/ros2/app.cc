#include "cactus_rt/ros2/app.h"

#include <rclcpp/executors/single_threaded_executor.hpp>
#include <rclcpp/rclcpp.hpp>

#include "cactus_rt/signal_handler.h"
#include "cactus_rt/utils.h"

namespace cactus_rt::ros2 {

cactus_rt::ThreadConfig Ros2ExecutorThread::CreateThreadConfig() {
  cactus_rt::CyclicThreadConfig thread_config;
  return thread_config;
}

Ros2ExecutorThread::Ros2ExecutorThread() : Thread("ROS2ExecutorThread", CreateThreadConfig()) {}

void Ros2ExecutorThread::Run() {
  rclcpp::ExecutorOptions options;
  auto                    node_ptr = ros2_adapter_->Node()->get_node_base_interface();
  options.context = node_ptr->get_context();
  executor_.emplace(options);
  executor_->add_node(node_ptr);
  while (!StopRequested()) {
    executor_->spin_once();
  }

  ros2_adapter_->DrainQueues();

  executor_->remove_node(node_ptr);
}

App::App(
  int                  argc,
  const char*          argv[],  // NOLINT
  std::string          name,
  cactus_rt::AppConfig config,
  Ros2Adapter::Config  ros2_adapter_config
) : cactus_rt::App(name, config) {
  rclcpp::init(argc, argv, rclcpp::InitOptions(), rclcpp::SignalHandlerOptions::None);

  cactus_rt::SetUpTerminationSignalHandler();

  signal_handling_thread_ = std::thread([this]() {
    cactus_rt::WaitForAndHandleTerminationSignal();

    RequestStop();
    Join();
    rclcpp::shutdown();
  });

  signal_handling_thread_.detach();

  // Must initialize rclcpp before making the Ros2Adapter;
  ros2_adapter_ = std::make_shared<Ros2Adapter>(name, ros2_adapter_config);
  ros2_executor_thread_ = CreateROS2EnabledThread<Ros2ExecutorThread>();
}

App::~App() {
  rclcpp::shutdown();
}

void App::Start(int64_t start_monotonic_time_ns) {
  // Start the Ros2ExecutorThread first. Don't think it is 100% necessary but why not get a head start.
  if (start_monotonic_time_ns == -1) {
    start_monotonic_time_ns = NowNs();
  }

  ros2_executor_thread_->Start(start_monotonic_time_ns);
  cactus_rt::App::Start(start_monotonic_time_ns);
}

void App::RequestStop() {
  // Stop all the registered threads first, then stop the Ros2ExecutorThread
  // after the normal threads are joined to ensure we flush messages. See App::Join.
  cactus_rt::App::RequestStop();
}

void App::Join() {
  // Join the registered threads first.
  cactus_rt::App::Join();

  // At this point, all threads are stopped. We need to stop the ros2 executor
  // thread as well.
  ros2_executor_thread_->RequestStop();
  ros2_executor_thread_->Join();
}

Ros2ThreadMixin::~Ros2ThreadMixin() = default;
}  // namespace cactus_rt::ros2
