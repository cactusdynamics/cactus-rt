#ifndef CACTUS_RT_ROS2_ROS2_ADAPTER_H_
#define CACTUS_RT_ROS2_ROS2_ADAPTER_H_

#include <readerwriterqueue.h>

#include <chrono>
#include <memory>
#include <mutex>
#include <rclcpp/rclcpp.hpp>
#include <string>
#include <vector>

#include "publisher.h"
#include "subscription.h"

namespace cactus_rt::ros2 {

class Ros2Adapter {
 public:
  struct Config {
    /**
     * The time interval for which the adapter node is polling for publisher data.
     */
    std::chrono::microseconds timer_interval = std::chrono::milliseconds(100);
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

  template <typename RealtimeT, typename RosT, bool CheckForTrivialRealtimeT = true>
  std::shared_ptr<Publisher<RealtimeT, RosT, CheckForTrivialRealtimeT>> CreatePublisher(
    const std::string& topic_name,
    const rclcpp::QoS& qos,
    size_t             rt_queue_size = 1000
  ) {
    auto publisher = Publisher<RealtimeT, RosT, CheckForTrivialRealtimeT>::Create(*ros_node_, topic_name, qos, rt_queue_size);

    const std::scoped_lock lock(mut_);
    publishers_.push_back(publisher);
    return publisher;
  }

  template <typename RealtimeT, typename RosT>
  std::shared_ptr<SubscriptionLatest<RealtimeT, RosT>> CreateSubscriptionForLatestValue(
    const std::string& topic_name,
    const rclcpp::QoS& qos
  ) {
    auto subscriber = SubscriptionLatest<RealtimeT, RosT>::Create(*this->ros_node_, topic_name, qos);

    const std::scoped_lock lock(mut_);
    subscriptions_.push_back(subscriber);
    return subscriber;
  }

 private:
  void TimerCallback();
  void DrainQueues();
};

}  // namespace cactus_rt::ros2

#endif
