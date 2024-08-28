#ifndef CACTUS_RT_ROS2_PUBLISHER_H_
#define CACTUS_RT_ROS2_PUBLISHER_H_

#include <readerwriterqueue.h>

#include <memory>
#include <rclcpp/rclcpp.hpp>
#include <type_traits>

#include "quill/Quill.h"

namespace cactus_rt::ros2 {
class Ros2Adapter;

class IPublisher {
  friend class Ros2Adapter;

  virtual bool   DequeueAndPublishToRos() = 0;
  virtual size_t FullyDrainAndPublishToRos() = 0;

 public:
  virtual ~IPublisher() = default;
};

template <typename RealtimeT, typename RosT, bool CheckForTrivialRealtimeT = true>
class Publisher : public IPublisher {
  friend class Ros2Adapter;

  static_assert(!CheckForTrivialRealtimeT || std::is_trivial_v<RealtimeT>, "RealtimeT must be a trivial object to be real-time safe");

  using NoConversion = std::is_same<RealtimeT, RosT>;
  using AdaptedRosType = typename std::conditional_t<NoConversion::value, RosT, rclcpp::TypeAdapter<RealtimeT, RosT>>;

  quill::Logger*                                        logger_;
  typename rclcpp::Publisher<AdaptedRosType>::SharedPtr publisher_;
  moodycamel::ReaderWriterQueue<RealtimeT>              queue_;

  bool DequeueAndPublishToRos() override {
    if constexpr (NoConversion::value) {
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
      RosT&                       ros_msg = loaned_msg.get();

      // Second copy
      AdaptedRosType::convert_to_ros_message(rt_msg, ros_msg);

      publisher_->publish(std::move(loaned_msg));
      return true;
    }
  }

  size_t FullyDrainAndPublishToRos() override {
    size_t count = 0;
    while (true) {
      if (!DequeueAndPublishToRos()) {
        return count;
      }
      count++;
    }
  }

  static std::shared_ptr<Publisher<RealtimeT, RosT, CheckForTrivialRealtimeT>> Create(
    quill::Logger*     logger,
    rclcpp::Node&      node,
    const std::string& topic_name,
    const rclcpp::QoS& qos,
    const size_t       rt_queue_size = 1000
  ) {
    return std::shared_ptr<Publisher<RealtimeT, RosT, CheckForTrivialRealtimeT>>(
      new Publisher<RealtimeT, RosT, CheckForTrivialRealtimeT>(
        logger,
        node.create_publisher<AdaptedRosType>(topic_name, qos),
        moodycamel::ReaderWriterQueue<RealtimeT>(rt_queue_size)
      )
    );
  }

  Publisher(
    quill::Logger*                                        logger,
    typename rclcpp::Publisher<AdaptedRosType>::SharedPtr publisher,
    moodycamel::ReaderWriterQueue<RealtimeT>&&            queue
  ) : logger_(logger), publisher_(publisher), queue_(std::move(queue)) {}

 public:
  template <typename... Args>
  bool Publish(Args&&... args) noexcept {
    const bool success = queue_.try_emplace(std::forward<Args>(args)...);
    // TODO: Keep track of success/failed messages and expose that to be queried

    if (!success) {
      LOG_WARNING_LIMIT(std::chrono::seconds(5), logger_, "failed to publish to {} due to full queue", publisher_->get_topic_name());
    }

    return success;
  }
};

}  // namespace cactus_rt::ros2

#endif
