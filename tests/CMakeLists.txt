find_package(GTest REQUIRED)

add_executable(cactus_rt_tests
  utils_test.cc
  tracing/single_threaded_test.cc
  tracing/multi_threaded_test.cc

  tracing/helpers/assert_helpers.cc
  tracing/helpers/mock_sink.cc
  tracing/helpers/mock_threads.cc
)

target_link_libraries(cactus_rt_tests
  PRIVATE
  cactus_rt
  cactus_tracing_embedded_perfetto_protos
  GTest::gtest
  GTest::gtest_main
)

setup_cactus_rt_target_options(cactus_rt_tests)

gtest_discover_tests(cactus_rt_tests)

find_package(benchmark REQUIRED)

add_executable(cactus_rt_tracing_benchmark
  tracing/tracing_benchmark.cc
)

target_link_libraries(cactus_rt_tracing_benchmark
  PRIVATE
  cactus_rt
  cactus_tracing_embedded_perfetto_protos
  benchmark::benchmark
)

setup_cactus_rt_target_options(cactus_rt_tracing_benchmark)
