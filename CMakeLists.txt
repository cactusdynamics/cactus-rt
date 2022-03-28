cmake_minimum_required(VERSION 3.13)
project(rt_demo)

set(USDT_SOURCE ${CMAKE_CURRENT_SOURCE_DIR}/src/probes.d)
set(USDT_HEADER ${CMAKE_CURRENT_BINARY_DIR}/generated/rt_demo_sdt.h)
set(USDT_OBJ ${CMAKE_CURRENT_BINARY_DIR}/generated/rt_demo_sdt.o)

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
find_package(Boost REQUIRED)
find_package(spdlog REQUIRED)

add_executable(rt_demo
  src/main.cc
  src/thread.cc
  src/rt_app.cc
  src/cyclic_rt_thread.cc
  src/low_freq_controller.cc
  src/high_freq_controller.cc
  src/data_monitor.cc
  src/utils/online_mean_tracker.cc
)

target_compile_features(rt_demo
  PUBLIC
  cxx_std_20
)

target_include_directories(rt_demo
  PRIVATE
  ${CMAKE_CURRENT_SOURCE_DIR}/include
  ${CMAKE_CURRENT_BINARY_DIR}/generated
)

target_link_libraries(rt_demo
  PRIVATE
  Threads::Threads
  spdlog::spdlog
  ${USDT_OBJ}
)

# USDT support

add_custom_target(rt_demo_usdt_header_clean
  COMMAND mkdir -p ${CMAKE_CURRENT_BINARY_DIR}/generated && rm -f ${USDT_HEADER}
  COMMENT "Remove generated USDT header"
)

add_custom_target(rt_demo_usdt_header
  COMMAND dtrace -h -s ${USDT_SOURCE} -o ${USDT_HEADER}
  COMMENT "Generate USDT probes header file"
)

# TODO: This is not great, as any file dependent on the usdt header will have
# to be compiled every single time when we compile, even if nothing changed,
# which is not great.
add_dependencies(rt_demo_usdt_header rt_demo_usdt_header_clean)

add_custom_target(rt_demo_usdt_obj_clean
  COMMAND mkdir -p ${CMAKE_CURRENT_BINARY_DIR}/generated && rm -f ${USDT_OBJ}
  COMMENT "Remove USDT probe object file"
)

add_custom_target(rt_demo_usdt_obj
  COMMAND dtrace -G -s ${USDT_SOURCE} -o ${USDT_OBJ}
  COMMENT "Generate USDT probes object file"
)

add_dependencies(rt_demo_usdt_obj rt_demo_usdt_obj_clean)
add_dependencies(rt_demo rt_demo_usdt_header rt_demo_usdt_obj)
