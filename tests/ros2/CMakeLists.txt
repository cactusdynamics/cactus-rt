find_package(ament_cmake_gtest REQUIRED)
find_package(rclcpp REQUIRED)
find_package(std_msgs REQUIRED)

ament_add_gtest(cactus_rt_ros2_tests
  ping_pong_test.cc
  ping_pong_ros_thread.cc
)

ament_target_dependencies(cactus_rt_ros2_tests
  rclcpp
  std_msgs
)

target_link_libraries(cactus_rt_ros2_tests
  cactus_rt
)

setup_cactus_rt_target_options(cactus_rt_ros2_tests)
