#ifndef CACTUS_RT_ROS2_SUBSCRIPTION_H_
#define CACTUS_RT_ROS2_SUBSCRIPTION_H_

#include <memory>
#include <rclcpp/rclcpp.hpp>
#include <type_traits>

#include "../experimental/lockless/spsc/realtime_readable_value.h"

// Note: ROS subscription dispatch is here: https://github.com/ros2/rclcpp/blob/e10728c/rclcpp/include/rclcpp/any_subscription_callback.hpp#L481
// We are using the TypeAdapter method.

namespace cactus_rt::ros2 {

class Ros2Adapter;

class ISubscription {
 public:
  virtual ~ISubscription() = default;
};

template <typename RealtimeT>
struct StampedValue {
  int64_t   id;
  RealtimeT value;

  StampedValue() = default;
  StampedValue(const int64_t i, const RealtimeT& v) : id(i), value(v) {}
};

template <typename RealtimeT, typename RosT, bool CheckForTrivialRealtimeT = true>
class SubscriptionLatest : public ISubscription {
  friend class Ros2Adapter;

  static_assert(!CheckForTrivialRealtimeT || std::is_trivial_v<RealtimeT>, "RealtimeT must be a trivial object to be real-time safe");

  using NoConversion = std::is_same<RealtimeT, RosT>;
  using AdaptedRosType = typename std::conditional_t<NoConversion::value, RosT, rclcpp::TypeAdapter<RealtimeT, RosT>>;

  using RealtimeReadableValue = cactus_rt::experimental::lockless::spsc::RealtimeReadableValue<StampedValue<RealtimeT>>;

  typename rclcpp::Subscription<AdaptedRosType>::SharedPtr ros_subscription_;
  int64_t                                                  current_msg_id_ = 0;
  RealtimeReadableValue                                    latest_value_;

  void SubscriptionCallback(const RealtimeT& rt_msg) {
    current_msg_id_++;  // Useful to detect message has changed by the real-time thread.

    // First copy
    const StampedValue<RealtimeT> stamped_value(current_msg_id_, rt_msg);

    // A second copy then an allocation
    // TODO: directly write to the value (perfect forwarding required).
    latest_value_.Write(stamped_value);
  }

  static std::shared_ptr<SubscriptionLatest<RealtimeT, RosT, CheckForTrivialRealtimeT>> Create(
    rclcpp::Node&      node,
    const std::string& topic_name,
    const rclcpp::QoS& qos
  ) {
    auto subscription = std::make_shared<SubscriptionLatest<RealtimeT, RosT, CheckForTrivialRealtimeT>>();

    subscription->ros_subscription_ = node.create_subscription<AdaptedRosType>(
      topic_name,
      qos,
      [subscription](const RealtimeT& rt_msg) {
        // TODO: we are capturing the subscription shared_ptr by value. Will this cause a memory leak?
        subscription->SubscriptionCallback(rt_msg);
      }
    );

    return subscription;
  }

 public:
  /**
   * @brief Do not use this method. Defined to allow make_shared to work.
   *
   * @private
   */
  SubscriptionLatest() = default;

  StampedValue<RealtimeT> ReadLatest() noexcept {
    return latest_value_.Read();
  }
};
}  // namespace cactus_rt::ros2

#endif
