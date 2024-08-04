find_package(ament_cmake REQUIRED)
find_package(rclcpp REQUIRED)

target_sources(cactus_rt
  PRIVATE
  src/cactus_rt/ros2/ros2_adapter.cc
  src/cactus_rt/ros2/app.cc
)

ament_target_dependencies(cactus_rt
  PUBLIC
  rclcpp
)

add_subdirectory(examples/ros2/publisher)
add_subdirectory(examples/ros2/subscriber)

ament_package()
