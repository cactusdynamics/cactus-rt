#include "cactus_rt/ros2/ros2_adapter.h"

#include <readerwriterqueue.h>

namespace cactus_rt::ros2 {

Ros2Adapter::Ros2Adapter(const std::string& name, const Ros2Adapter::Config& config)
    : ros_node_(std::make_shared<rclcpp::Node>(name + "_ros_adapter")),
      logger_(quill::create_logger("Ros2Adapter")) {
  timer_ = this->ros_node_->create_wall_timer(config.timer_interval, [this] { TimerCallback(); });
}

void Ros2Adapter::TimerCallback() {
  DrainQueues();
}

void Ros2Adapter::DrainQueues() {
  const std::scoped_lock lock(mut_);

  bool has_data = true;
  while (has_data) {
    has_data = false;

    for (const auto& publisher : publishers_) {
      if (publisher->DequeueAndPublishToRos()) {
        has_data = true;
      }
    }
  }
}

}  // namespace cactus_rt::ros2
