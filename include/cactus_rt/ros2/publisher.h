#ifndef CACTUS_RT_ROS2_PUBLISHER_H_
#define CACTUS_RT_ROS2_PUBLISHER_H_

#include <readerwriterqueue.h>

#include <optional>
#include <rclcpp/rclcpp.hpp>

#include "types.h"

namespace cactus_rt::ros2 {
class Ros2Adapter;

class IPublisher {
  friend class Ros2Adapter;

  virtual bool DequeueAndPublishToRos() = 0;
  virtual void FullyDrainAndPublishToRos() = 0;

 public:
  virtual ~IPublisher() = default;
};

template <typename RealtimeT, typename RosT>
class Publisher : public IPublisher {
  typename rclcpp::Publisher<RosT>::SharedPtr             publisher_;
  std::optional<RealtimeToROS2Converter<RealtimeT, RosT>> converter_;
  moodycamel::ReaderWriterQueue<RealtimeT>                queue_;

  bool DequeueAndPublishToRos() override {
    RealtimeT rt_msg;

    // 1 copy
    const bool has_data = queue_.try_dequeue(rt_msg);
    if (!has_data) {
      return false;
    }

    if (converter_) {
      auto loaned_msg = publisher_->borrow_loaned_message();
      // 1 copy
      converter_.value()(rt_msg, loaned_msg.get());
      publisher_->publish(std::move(loaned_msg));
    } else {
      if constexpr (std::is_same_v<RealtimeT, RosT>) {
        const auto* ros_msg = static_cast<const RosT*>(rt_msg);
        // 1 copy
        publisher_->publish(*ros_msg);
      } else {
        throw std::invalid_argument{"converter not specified but RealtimeT and RosT are not the same?!"};
      }
    }

    return true;
  }

  void FullyDrainAndPublishToRos() override {
    while (true) {
      const auto has_data = DequeueAndPublishToRos();
      if (!has_data) {
        break;
      }
    }
  }

 public:
  /**
   * Constructs a publisher. Shouldn't be called directly. Only public to enable make_shared.
   *
   * @private
   */
  Publisher(
    typename rclcpp::Publisher<RosT>::SharedPtr             publisher,
    std::optional<RealtimeToROS2Converter<RealtimeT, RosT>> converter,
    moodycamel::ReaderWriterQueue<RealtimeT>&&              queue
  ) : publisher_(publisher), converter_(converter), queue_(std::move(queue)) {}

  template <typename... Args>
  bool Publish(Args&&... args) noexcept {
    const bool success = queue_.try_emplace(std::forward<Args>(args)...);
    // TODO: Keep track of success/failed messages and expose that to be queried
    return success;
  }
};

}  // namespace cactus_rt::ros2

#endif
