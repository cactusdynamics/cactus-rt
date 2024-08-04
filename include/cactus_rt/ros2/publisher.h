#ifndef CACTUS_RT_ROS2_PUBLISHER_H_
#define CACTUS_RT_ROS2_PUBLISHER_H_

#include <readerwriterqueue.h>

#include <rclcpp/rclcpp.hpp>
#include <type_traits>

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
  friend class Ros2Adapter;

  static_assert(std::is_trivial_v<RealtimeT>, "RealtimeT must be a trivial object to be real-time safe");
  using AdaptedRosType = rclcpp::TypeAdapter<RealtimeT, RosT>;

  typename rclcpp::Publisher<AdaptedRosType>::SharedPtr publisher_;
  moodycamel::ReaderWriterQueue<RealtimeT>              queue_;

  bool DequeueAndPublishToRos() override {
    if constexpr (std::is_same_v<RealtimeT, RosT>) {
      rclcpp::LoanedMessage<RealtimeT> loaned_msg = publisher_->borrow_loaned_message();

      RealtimeT& rt_msg = loaned_msg.get();
      // First copy
      if (!queue_.try_dequeue(rt_msg)) {
        return false;
      }

      publisher_->publish(std::move(loaned_msg));
      return true;
    } else {
      RealtimeT rt_msg;
      // First copy
      if (!queue_.try_dequeue(rt_msg)) {
        return false;
      }

      // Possible allocation if middleware requires it.
      rclcpp::LoanedMessage<RosT> loaned_msg = publisher_->borrow_loaned_message();

      // Second copy
      AdaptedRosType::convert_to_ros_message(rt_msg, loaned_msg.get());

      publisher_->publish(std::move(loaned_msg));
      return true;
    }
  }

  void FullyDrainAndPublishToRos() override {
    while (true) {
      const auto has_data = DequeueAndPublishToRos();
      if (!has_data) {
        break;
      }
    }
  }

  static std::shared_ptr<Publisher<RealtimeT, RosT>> Create(
    rclcpp::Node&      node,
    const std::string& topic_name,
    const rclcpp::QoS& qos,
    const size_t       rt_queue_size = 1000
  ) {
    typename rclcpp::Publisher<AdaptedRosType>::SharedPtr publisher = node.create_publisher<AdaptedRosType>(topic_name, qos);
    typename moodycamel::ReaderWriterQueue<RealtimeT>     queue(rt_queue_size);

    return std::make_shared<Publisher<RealtimeT, RosT>>(
      std::move(publisher),
      std::move(queue)
    );
  }

 public:
  /**
   * Constructs a publisher. Shouldn't be called directly. Only public to enable make_shared.
   *
   * @private
   */
  Publisher(
    typename rclcpp::Publisher<AdaptedRosType>::SharedPtr publisher,
    moodycamel::ReaderWriterQueue<RealtimeT>&&            queue
  ) : publisher_(publisher), queue_(std::move(queue)) {}

  template <typename... Args>
  bool Publish(Args&&... args) noexcept {
    const bool success = queue_.try_emplace(std::forward<Args>(args)...);
    // TODO: Keep track of success/failed messages and expose that to be queried
    return success;
  }
};

}  // namespace cactus_rt::ros2

#endif
