add_executable(rt_ros2_example
  main.cc
)

target_link_libraries(rt_ros2_example
  PRIVATE
  cactus_rt
)

setup_cactus_rt_target_options(rt_ros2_example)

install(
  TARGETS rt_ros2_example
  DESTINATION lib/${PROJECT_NAME}
)
