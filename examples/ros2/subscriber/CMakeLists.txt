find_package(std_msgs REQUIRED)

add_executable(rt_ros2_subscriber
  main.cc
)

target_link_libraries(rt_ros2_subscriber
  PRIVATE
  cactus_rt
)

setup_cactus_rt_target_options(rt_ros2_subscriber)

ament_target_dependencies(rt_ros2_subscriber
  PUBLIC
  std_msgs
)

install(
  TARGETS rt_ros2_subscriber
  DESTINATION lib/${PROJECT_NAME}
)

