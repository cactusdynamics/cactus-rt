cmake_minimum_required(VERSION 3.13)
project(rt_demo)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

option(ENABLE_CLANG_TIDY "Run clang-tidy" OFF)
option(ENABLE_EXAMPLES "Build example programs" ON)

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

if (ENABLE_CLANG_TIDY)
  find_program(CLANG_TIDY clang-tidy clang-tidy-14 clang-tidy-13 clang-tidy-12 clang-tidy-11)
  set(CMAKE_CXX_CLANG_TIDY ${CLANG_TIDY})
else()
  message(STATUS "Not running clang-tidy. Use ENABLE_CLANG_TIDY=ON to run clang-tidy.")
endif()

add_subdirectory(libs/rt)

if (ENABLE_EXAMPLES)
  message(STATUS "Building example programs. Turn it off via ENABLE_EXAMPLES=OFF")
  add_subdirectory(examples/simple_example)
  add_subdirectory(examples/message_passing_example)
  add_subdirectory(examples/mutex_example)
  add_subdirectory(examples/lttng_ust_example)
endif()
