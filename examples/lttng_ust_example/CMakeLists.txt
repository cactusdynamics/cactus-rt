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
  LTTng::UST
)

if (ENABLE_CLANG_TIDY)
  # set_target_properties(rt_lttng_ust_example PROPERTIES CXX_CLANG_TIDY ${CLANG_TIDY})
endif()

install(
  TARGETS rt_lttng_ust_example
  DESTINATION bin
)
