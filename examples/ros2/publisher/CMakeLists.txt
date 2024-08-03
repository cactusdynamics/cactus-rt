find_package(std_msgs REQUIRED)

add_executable(rt_ros2_publisher
  main.cc
)

target_link_libraries(rt_ros2_publisher
  PRIVATE
  cactus_rt
)

setup_cactus_rt_target_options(rt_ros2_publisher)

ament_target_dependencies(rt_ros2_publisher
  PUBLIC
  std_msgs
)

install(
  TARGETS rt_ros2_publisher
  DESTINATION lib/${PROJECT_NAME}
)
