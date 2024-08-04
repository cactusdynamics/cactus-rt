#ifndef CACTUS_RT_ROS2_SUBSCRIPTION_H_
#define CACTUS_RT_ROS2_SUBSCRIPTION_H_

#include <memory>
#include <optional>
#include <rclcpp/rclcpp.hpp>

#include "../experimental/lockless/spsc/realtime_readable_value.h"
#include "cactus_rt/utils.h"
#include "types.h"

// Note: ROS subscription dispatch is here: https://github.com/ros2/rclcpp/blob/e10728c/rclcpp/include/rclcpp/any_subscription_callback.hpp#L481
// There are many methods that we can choose from.

namespace cactus_rt::ros2 {

class Ros2Adapter;

class ISubscription {
 public:
  virtual ~ISubscription() = default;
};

template <typename RealtimeT>
struct StampedValue {
  int64_t   received_time;  // TODO: need to align this with elapsed time from the threads...
  RealtimeT value;

  StampedValue() = default;
  StampedValue(int64_t t, const RealtimeT& v) : received_time(t), value(v) {}
};

// TODO: Theoretically it is possible to not use the type converter if we don't
// copy the data on read with RealtimeReadableValue.
template <typename RealtimeT, typename RosT>
class SubscriptionLatest : public ISubscription {
  friend class Ros2Adapter;

  using RealtimeReadableValue = cactus_rt::experimental::lockless::spsc::RealtimeReadableValue<StampedValue<RealtimeT>>;

  typename rclcpp::Subscription<RosT>::SharedPtr          ros_subscription_;
  std::optional<Ros2ToRealtimeConverter<RealtimeT, RosT>> converter_;
  RealtimeReadableValue                                   latest_value_;

  void SubscriptionCallback(const RosT& ros_msg) {
    if (converter_) {
      const RealtimeT& rt_msg = converter_.value()(ros_msg);

      // 1 copy
      const StampedValue<RealtimeT> stamped_value(NowNs(), rt_msg);

      // 1 allocation and 1 copy.
      latest_value_.Write(stamped_value);
    } else {
      if constexpr (std::is_same_v<RealtimeT, RosT>) {
        const auto& rt_msg = static_cast<const RealtimeT&>(ros_msg);

        // 1 copy
        const StampedValue<RealtimeT> stamped_value(NowNs(), rt_msg);

        // 1 allocation and 1 copy.
        latest_value_.Write(stamped_value);
      } else {
        throw std::invalid_argument{"converter not specified but RealtimeT and RosT are not the same?!"};
      }
    }
  }

  static std::shared_ptr<SubscriptionLatest> Create(
    rclcpp::Node&                                           node,
    const std::string&                                      topic_name,
    const rclcpp::QoS&                                      qos,
    std::optional<Ros2ToRealtimeConverter<RealtimeT, RosT>> converter
  ) {
    auto subscription = std::make_shared<SubscriptionLatest<RealtimeT, RosT>>(converter);

    auto* subscription_ptr = subscription.get();

    // TODO: is there a better way to do this under than to capture the shared_pointer like this?
    subscription->ros_subscription_ = node.create_subscription<RosT>(topic_name, qos, [subscription_ptr](const RosT& ros_msg) {
      subscription_ptr->SubscriptionCallback(ros_msg);
    });

    return subscription;
  }

 public:
  /**
   * Constructs a subscription. Shouldn't be called directly. Only public to enable make_shared.
   *
   * @private
   */
  explicit SubscriptionLatest(
    std::optional<Ros2ToRealtimeConverter<RealtimeT, RosT>> converter
  ) : converter_(converter) {}

  inline StampedValue<RealtimeT> ReadLatest() noexcept {
    return latest_value_.Read();
  }
};
}  // namespace cactus_rt::ros2

#endif
