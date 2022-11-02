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

if (ENABLE_CLANG_TIDY)
  set_target_properties(rt_mutex_example PROPERTIES CXX_CLANG_TIDY ${CLANG_TIDY})
endif()

install(
  TARGETS rt_mutex_example
  DESTINATION bin
)
