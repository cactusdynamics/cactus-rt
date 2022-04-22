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
  -O3
)

add_subdirectory(libs/rt)

add_executable(rt_default_demo
  examples/default_example/main.cc
)

target_link_libraries(rt_default_demo
  PRIVATE
  rt_app_lib
)

