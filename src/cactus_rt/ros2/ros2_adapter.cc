#include "cactus_rt/ros2/ros2_adapter.h"

#include <readerwriterqueue.h>

namespace cactus_rt::ros2 {

IPublisher::~IPublisher() = default;

Ros2Adapter::Ros2Adapter(const std::string& name, const Ros2Adapter::Config& config)
    : ros_node_(std::make_shared<rclcpp::Node>(name + "_ros_adapter")) {
  timer_ = this->ros_node_->create_wall_timer(config.timer_interval, [this] { TimerCallback(); });
}

void Ros2Adapter::TimerCallback() {
  DrainQueues();
}

void Ros2Adapter::DrainQueues() {
  const std::scoped_lock lock(mut_);

  for (const auto& publisher : publishers_) {
    // Hopefully the thread is not publishing so quickly that a single
    // publisher monopolizes all resources. That said, if that happens the
    // program is likely in bigger trouble anyway.
    //
    // TODO: make it so we dequeue once.
    publisher->FullyDrainAndPublishToRos();
  }
}

}  // namespace cactus_rt::ros2
