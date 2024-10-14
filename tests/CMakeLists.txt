find_package(GTest REQUIRED)

enable_testing()

add_executable(cactus_rt_tests
  utils_test.cc
  experimental/random_test.cc
  experimental/lockless/atomic_bitset_test.cc
  experimental/lockless/spsc/realtime_readable_value_test.cc
  experimental/lockless/spsc/realtime_writable_value_test.cc
)

target_link_libraries(cactus_rt_tests
  PRIVATE
  cactus_rt
  GTest::gtest
  GTest::gtest_main
)

setup_cactus_rt_target_options(cactus_rt_tests)

target_compile_definitions(cactus_rt_tests
  PRIVATE
  $<$<CONFIG:Debug>:DEBUG_BUILD>
  $<$<CONFIG:RelWithDebInfo>:RELEASE_BUILD>
  $<$<CONFIG:Release>:RELEASE_BUILD>
  $<$<CONFIG:MinSizeRel>:RELEASE_BUILD>
)

gtest_discover_tests(cactus_rt_tests)

if(CACTUS_RT_ENABLE_TRACING)
  add_executable(cactus_rt_tracing_tests

    tracing/single_threaded_test.cc
    tracing/string_interner_test.cc
    tracing/multi_threaded_test.cc

    tracing/helpers/assert_helpers.cc
    tracing/helpers/mock_sink.cc
    tracing/helpers/mock_threads.cc
  )

  target_link_libraries(cactus_rt_tracing_tests
    PRIVATE
    cactus_rt
    cactus_tracing_embedded_perfetto_protos
    GTest::gtest
    GTest::gtest_main
  )

  setup_cactus_rt_target_options(cactus_rt_tracing_tests)

  gtest_discover_tests(cactus_rt_tracing_tests)
endif()

find_package(benchmark REQUIRED)

add_executable(cactus_rt_tracing_benchmark
  tracing/tracing_benchmark.cc
)

if (CACTUS_RT_ENABLE_TRACING)
  target_sources(cactus_rt_tracing_benchmark
    PRIVATE
    tracing/string_interner_benchmark.cc
  )
endif()

target_link_libraries(cactus_rt_tracing_benchmark
  PRIVATE
  cactus_rt
  benchmark::benchmark
)

setup_cactus_rt_target_options(cactus_rt_tracing_benchmark)
