cmake_minimum_required(VERSION 3.13)
project(rt_demo)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

add_compile_options(
  -Wall
  -Wextra
  -Wpedantic
  -Wshadow
  -Wnon-virtual-dtor
  -Wpedantic
  -Wold-style-cast
  -Wcast-align
  -Wunused
  -Woverloaded-virtual
  -Wsign-conversion
  -Wmisleading-indentation
  -Wduplicated-cond
  -Wduplicated-branches
  -Wnull-dereference
  -Wuseless-cast
  -Wdouble-promotion
  -g
  -O3
)

add_definitions(-DSPDLOG_ACTIVE_LEVEL=1) # debug level

set(CMAKE_CXX_CLANG_TIDY clang-tidy)

add_subdirectory(libs/rt)
add_subdirectory(examples/simple_example)
add_subdirectory(examples/message_passing_example)
add_subdirectory(examples/mutex_example)
add_subdirectory(examples/lttng_ust_example)
