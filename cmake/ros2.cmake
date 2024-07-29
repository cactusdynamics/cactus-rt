find_package(ament_cmake REQUIRED)
find_package(rclcpp REQUIRED)

ament_target_dependencies(cactus_rt
  PUBLIC
  rclcpp
)

add_subdirectory(examples/ros2_example)

ament_package()
