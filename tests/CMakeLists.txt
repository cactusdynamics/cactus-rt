find_package(GTest REQUIRED)

add_executable(cactus_rt_tests
  utils_test.cc
  tracing/tracing_test.cc
)

target_include_directories(cactus_rt_tests
  PRIVATE
  ${CMAKE_SOURCE_DIR}/include
)

target_link_libraries(cactus_rt_tests
  PRIVATE
  cactus_rt
  cactus_tracing_embedded_perfetto_protos
  GTest::gtest
  GTest::gtest_main
)

gtest_discover_tests(cactus_rt_tests)
