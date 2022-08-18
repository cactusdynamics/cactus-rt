find_package(spdlog REQUIRED)
find_package(LTTngUST REQUIRED)

add_executable(rt_lttng_ust_example
  src/tracepoint_provider.cc
  src/main.cc
)

target_include_directories(rt_lttng_ust_example
  PRIVATE
  include
)

target_link_libraries(rt_lttng_ust_example
  PRIVATE
  cactus_rt
  spdlog::spdlog
  LTTng::UST
)

install(
  TARGETS rt_lttng_ust_example
  DESTINATION bin
)
