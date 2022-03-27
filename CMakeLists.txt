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
)

# https://stackoverflow.com/questions/5395309/how-do-i-force-cmake-to-include-pthread-option-during-compilation
set(CMAKE_THREAD_PREFER_PTHREAD TRUE)
set(THREADS_PREFER_PTHREAD_FLAG TRUE)
find_package(Threads REQUIRED)
find_package(Boost REQUIRED)
find_package(spdlog REQUIRED)

add_executable(rt_demo
  src/main.cc
  src/thread.cc
  src/rt_app.cc
  src/low_freq_controller.cc
  src/high_freq_controller.cc
  src/data_monitor.cc
)

target_compile_features(rt_demo
  PUBLIC
  cxx_std_20
)

target_include_directories(rt_demo
  PRIVATE
  $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
  $<INSTALL_INTERFACE:include>
)

target_link_libraries(rt_demo
  PRIVATE
  Threads::Threads
  spdlog::spdlog
)

