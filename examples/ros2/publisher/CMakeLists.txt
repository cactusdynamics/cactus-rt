find_package(std_msgs REQUIRED)

add_executable(rt_ros2_publisher_complex_data
  complex_data.cc
)

target_link_libraries(rt_ros2_publisher_complex_data
  PRIVATE
  cactus_rt
)

setup_cactus_rt_target_options(rt_ros2_publisher_complex_data)

ament_target_dependencies(rt_ros2_publisher_complex_data
  PUBLIC
  std_msgs
)

install(
  TARGETS rt_ros2_publisher_complex_data
  DESTINATION lib/${PROJECT_NAME}
)

add_executable(rt_ros2_publisher_simple_data
  simple_data.cc
)

target_link_libraries(rt_ros2_publisher_simple_data
  PRIVATE
  cactus_rt
)

setup_cactus_rt_target_options(rt_ros2_publisher_simple_data)

ament_target_dependencies(rt_ros2_publisher_simple_data
  PUBLIC
  std_msgs
)

install(
  TARGETS rt_ros2_publisher_simple_data
  DESTINATION lib/${PROJECT_NAME}
)
