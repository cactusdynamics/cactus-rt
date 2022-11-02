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

if (ENABLE_CLANG_TIDY)
  set_target_properties(rt_message_passing_example PROPERTIES CXX_CLANG_TIDY ${CLANG_TIDY})
endif()

install(
  TARGETS rt_message_passing_example
  DESTINATION bin
)
