find_package(GTest REQUIRED)

add_executable(cactus_rt_tests
  utils_test.cc
)

target_include_directories(cactus_rt_tests
  PRIVATE
  ${CMAKE_SOURCE_DIR}/include
)

target_link_libraries(cactus_rt_tests
  PRIVATE
  GTest::gtest
  GTest::gtest_main
)

gtest_discover_tests(cactus_rt_tests)
