cmake_minimum_required(VERSION 3.13)
project(rt_setup_demo)

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

# https://stackoverflow.com/questions/5395309/how-do-i-force-cmake-to-include-pthread-option-during-compilation
set(CMAKE_THREAD_PREFER_PTHREAD TRUE)
set(THREADS_PREFER_PTHREAD_FLAG TRUE)
find_package(Threads REQUIRED)
find_package(spdlog REQUIRED)

add_executable(rt_setup_demo
  src/main.cc
  src/rt/thread.cc
  src/rt/app.cc
  src/rt/cyclic_rt_thread.cc
)

set_target_properties(rt_setup_demo
  PROPERTIES
  CXX_CLANG_TIDY clang-tidy
)

target_compile_features(rt_setup_demo
  PUBLIC
  cxx_std_20
)

target_include_directories(rt_setup_demo
  PRIVATE
  ${CMAKE_CURRENT_SOURCE_DIR}/include
  ${CMAKE_CURRENT_BINARY_DIR}/generated
)

target_link_libraries(rt_setup_demo
  PRIVATE
  Threads::Threads
  spdlog::spdlog
)
