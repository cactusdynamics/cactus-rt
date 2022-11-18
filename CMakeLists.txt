cmake_minimum_required(VERSION 3.18)
project(cactus_rt)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

option(ENABLE_CLANG_TIDY "Run clang-tidy" OFF)
option(ENABLE_EXAMPLES "Build example programs" ON)

add_definitions(-DSPDLOG_ACTIVE_LEVEL=1) # debug level

# https://stackoverflow.com/questions/5395309/how-do-i-force-cmake-to-include-pthread-option-during-compilation
set(CMAKE_THREAD_PREFER_PTHREAD TRUE)
set(THREADS_PREFER_PTHREAD_FLAG TRUE)
find_package(Threads REQUIRED)
find_package(spdlog REQUIRED)

add_library(cactus_rt
  STATIC
  src/app.cc
  src/latency_tracker.cc
)

target_compile_features(cactus_rt
  PUBLIC
  cxx_std_20
)

target_include_directories(cactus_rt
  PUBLIC
  ${CMAKE_CURRENT_SOURCE_DIR}/include
)

target_link_libraries(cactus_rt
  PRIVATE
  Threads::Threads
  spdlog::spdlog
)

target_compile_options(cactus_rt
  PUBLIC # TODO: This should affect all the example programs as well, not sure if it this is a good idea tho
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
  -g # TODO: release vs debug
)

# Only enable clang-tidy and ctest if this is the main project and not being included further.
if(${CMAKE_PROJECT_NAME} STREQUAL ${PROJECT_NAME})
  include(CTest)

  if (ENABLE_CLANG_TIDY)
    find_program(CLANG_TIDY_PATH clang-tidy clang-tidy-14 clang-tidy-13 clang-tidy-12 clang-tidy-11)
    set_target_properties(cactus_rt PROPERTIES CXX_CLANG_TIDY ${CLANG_TIDY_PATH})
  else()
    message(STATUS "Not running clang-tidy. Use ENABLE_CLANG_TIDY=ON to run clang-tidy.")
  endif()

  if (BUILD_TESTING)
    add_subdirectory(tests)
  endif()

  if (ENABLE_EXAMPLES)
    message(STATUS "Building example programs. Turn it off via ENABLE_EXAMPLES=OFF")
    add_subdirectory(examples/simple_example)
    add_subdirectory(examples/message_passing_example)
    add_subdirectory(examples/mutex_example)
    add_subdirectory(examples/lttng_ust_example)
    add_subdirectory(examples/simple_deadline_example)
    add_subdirectory(examples/iceoryx_example)
  endif()
endif()
