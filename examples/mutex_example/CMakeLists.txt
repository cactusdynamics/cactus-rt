find_package(spdlog REQUIRED)

add_executable(rt_mutex_example
  src/main.cc
)

target_include_directories(rt_mutex_example
  PRIVATE
  include
)

target_link_libraries(rt_mutex_example
  PRIVATE
  cactus_rt
  spdlog::spdlog
)
