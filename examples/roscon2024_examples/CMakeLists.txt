add_executable(cactus_rt_roscon2024_simple_example
  simple_example.cc
)

target_link_libraries(cactus_rt_roscon2024_simple_example
  PRIVATE
  cactus_rt
)

setup_cactus_rt_target_options(cactus_rt_roscon2024_simple_example)

find_package(geometry_msgs REQUIRED)

add_executable(cactus_rt_roscon2024_ros_example
  ros_example.cc
)

target_link_libraries(cactus_rt_roscon2024_ros_example
  PRIVATE
  cactus_rt
)

setup_cactus_rt_target_options(cactus_rt_roscon2024_ros_example)

ament_target_dependencies(cactus_rt_roscon2024_ros_example
  PUBLIC
  geometry_msgs
)

install(
  TARGETS cactus_rt_roscon2024_ros_example
  DESTINATION lib/${PROJECT_NAME}
)
