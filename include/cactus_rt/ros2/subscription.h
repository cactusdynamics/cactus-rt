#ifndef CACTUS_RT_ROS2_SUBSCRIPTION_H_
#define CACTUS_RT_ROS2_SUBSCRIPTION_H_

#include <readerwriterqueue.h>

#include <memory>
#include <optional>
#include <rclcpp/rclcpp.hpp>
#include <type_traits>

#include "../experimental/lockless/spsc/realtime_readable_value.h"
#include "cactus_rt/logging.h"

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

  cactus_rt::logging::Logger*                              logger_;
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
    cactus_rt::logging::Logger* logger,
    rclcpp::Node&               node,
    const std::string&          topic_name,
    const rclcpp::QoS&          qos
  ) {
    std::shared_ptr<SubscriptionLatest<RealtimeT, RosT, CheckForTrivialRealtimeT>> subscription(
      new SubscriptionLatest<RealtimeT, RosT, CheckForTrivialRealtimeT>(logger)
    );

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

  explicit SubscriptionLatest(cactus_rt::logging::Logger* logger) : logger_(logger) {}

 public:
  StampedValue<RealtimeT> ReadLatest() noexcept {
    return latest_value_.Read();
  }
};

template <typename RealtimeT, typename RosT, bool CheckForTrivialRealtimeT = true>
class SubscriptionQueued : public ISubscription {
  friend class Ros2Adapter;

  static_assert(!CheckForTrivialRealtimeT || std::is_trivial_v<RealtimeT>, "RealtimeT must be a trivial object to be real-time safe");

  using NoConversion = std::is_same<RealtimeT, RosT>;
  using AdaptedRosType = typename std::conditional_t<NoConversion::value, RosT, rclcpp::TypeAdapter<RealtimeT, RosT>>;

  using Queue = moodycamel::ReaderWriterQueue<StampedValue<RealtimeT>>;

  cactus_rt::logging::Logger*                              logger_;
  typename rclcpp::Subscription<AdaptedRosType>::SharedPtr ros_subscription_;
  int64_t                                                  current_msg_id_ = 0;
  Queue                                                    queue_;

  void SubscriptionCallback(const RealtimeT& rt_msg) {
    current_msg_id_++;  // Useful to detect message has changed by the real-time thread.

    // A copy directly into the queue.
    // TODO: warn that we are losing data?
    queue_.try_emplace(current_msg_id_, rt_msg);
  }

  static std::shared_ptr<SubscriptionQueued<RealtimeT, RosT, CheckForTrivialRealtimeT>> Create(
    cactus_rt::logging::Logger* logger,
    rclcpp::Node&               node,
    const std::string&          topic_name,
    const rclcpp::QoS&          qos,
    const size_t                rt_queue_size = 1000
  ) {
    std::shared_ptr<SubscriptionQueued<RealtimeT, RosT, CheckForTrivialRealtimeT>> subscription(
      new SubscriptionQueued<RealtimeT, RosT, CheckForTrivialRealtimeT>(
        logger,
        moodycamel::ReaderWriterQueue<StampedValue<RealtimeT>>(rt_queue_size)
      )
    );

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

  SubscriptionQueued(
    cactus_rt::logging::Logger*                              logger,
    moodycamel::ReaderWriterQueue<StampedValue<RealtimeT>>&& queue
  ) : logger_(logger), queue_(std::move(queue)) {}

 public:
  std::optional<StampedValue<RealtimeT>> Read() noexcept {
    StampedValue<RealtimeT> v;
    if (queue_.try_dequeue(v)) {
      return v;
    }

    return std::nullopt;
  }
};

}  // namespace cactus_rt::ros2

#endif
