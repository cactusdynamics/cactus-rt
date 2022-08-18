find_package(Boost REQUIRED)
find_package(spdlog REQUIRED)

add_executable(rt_message_passing_example
  src/main.cc
  src/rt_thread.cc
  src/data_logger.cc
)

target_include_directories(rt_message_passing_example
  PRIVATE
  include
)

target_link_libraries(rt_message_passing_example
  PRIVATE
  cactus_rt
  spdlog::spdlog
  stdc++fs
)

install(
  TARGETS rt_message_passing_example
  DESTINATION bin
)
