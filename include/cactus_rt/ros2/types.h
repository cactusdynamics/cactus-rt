#ifndef CACTUS_RT_ROS2_TYPES_H_
#define CACTUS_RT_ROS2_TYPES_H_

#include <functional>

namespace cactus_rt::ros2 {
template <typename RealtimeT, typename RosT>
using Ros2ToRealtimeConverter = std::function<RealtimeT(const RosT&)>;

template <typename RealtimeT, typename RosT>
using RealtimeToROS2Converter = std::function<void(const RealtimeT&, RosT&)>;
}  // namespace cactus_rt::ros2

#endif
