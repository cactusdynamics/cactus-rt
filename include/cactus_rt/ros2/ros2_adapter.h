#ifndef CACTUS_RT_ROS2_ROS2_ADAPTER_H_
#define CACTUS_RT_ROS2_ROS2_ADAPTER_H_

#include <readerwriterqueue.h>

#include <chrono>
#include <memory>
#include <mutex>
#include <rclcpp/rclcpp.hpp>
#include <stdexcept>
#include <string>
#include <type_traits>
#include <utility>

#include "./publisher.h"
#include "./subscription.h"
#include "cactus_rt/ros2/subscription.h"
#include "cactus_rt/ros2/types.h"

namespace cactus_rt::ros2 {

class Ros2Adapter {
 public:
  struct Config {
    /**
     * The time interval for which the adapter node is polling for publisher data.
     */
    std::chrono::microseconds timer_interval = std::chrono::microseconds(200'000);
  };

 private:
  std::string node_name_;

  std::shared_ptr<rclcpp::Node> ros_node_;

  rclcpp::TimerBase::SharedPtr timer_;

  // Protects the vector of subscribers, publishers, and services
  // This means that during the timer callback, no subscribers, publishers, services, and etc. can be changed.
  std::mutex mut_;

  // Publishers and subscriptions
  std::vector<std::shared_ptr<IPublisher>>    publishers_;
  std::vector<std::shared_ptr<ISubscription>> subscriptions_;

 public:
  Ros2Adapter(const std::string& name_, const Config& config);

  std::shared_ptr<rclcpp::Node> Node() const {
    return ros_node_;
  }

  template <typename RealtimeT, typename RosT>
  std::shared_ptr<Publisher<RealtimeT, RosT>> CreatePublisher(
    const std::string&                                      topic_name,
    const rclcpp::QoS&                                      qos,
    std::optional<RealtimeToROS2Converter<RealtimeT, RosT>> converter,
    size_t                                                  rt_queue_size = 1000
  ) {
    if (!converter) {
      if constexpr (!(std::is_trivial_v<RosT> && std::is_standard_layout_v<RosT> && std::is_same_v<RosT, RealtimeT>)) {
        throw std::invalid_argument("RosT and RealtimeT must be the same and must be a plain object for converter not to be specified");
      }
    }

    typename rclcpp::Publisher<RosT>::SharedPtr       publisher = this->ros_node_->create_publisher<RosT>(topic_name, qos);
    typename moodycamel::ReaderWriterQueue<RealtimeT> queue{rt_queue_size};

    auto publisher_bundle = std::make_shared<Publisher<RealtimeT, RosT>>(
      std::move(publisher),
      converter,
      std::move(queue)
    );

    const std::scoped_lock lock(mut_);
    publishers_.push_back(publisher_bundle);
    return publisher_bundle;
  }

  template <typename RealtimeT, typename RosT>
  std::shared_ptr<SubscriptionLatest<RealtimeT, RosT>> CreateSubscriptionForLatestValue(
    const std::string&                                      topic_name,
    const rclcpp::QoS&                                      qos,
    std::optional<Ros2ToRealtimeConverter<RealtimeT, RosT>> converter
  ) {
    if (!converter) {
      if constexpr (!(std::is_trivial_v<RosT> && std::is_standard_layout_v<RosT> && std::is_same_v<RosT, RealtimeT>)) {
        throw std::invalid_argument("RosT and RealtimeT must be the same and must be a plain object for converter not to be specified");
      }
    }

    auto subscription_bundle = SubscriptionLatest<RealtimeT, RosT>::Create(*this->ros_node_, topic_name, qos, converter);

    const std::scoped_lock lock(mut_);
    subscriptions_.push_back(subscription_bundle);
    return subscription_bundle;
  }

 private:
  void TimerCallback();
  void DrainQueues();
};

}  // namespace cactus_rt::ros2

#endif
