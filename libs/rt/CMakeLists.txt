# https://stackoverflow.com/questions/5395309/how-do-i-force-cmake-to-include-pthread-option-during-compilation
set(CMAKE_THREAD_PREFER_PTHREAD TRUE)
set(THREADS_PREFER_PTHREAD_FLAG TRUE)
find_package(Threads REQUIRED)
find_package(spdlog REQUIRED)

add_library(rt_app_lib
  STATIC
  src/thread.cc
  src/app.cc
  src/cyclic_fifo_thread.cc
  src/latency_tracker.cc
)

target_compile_features(rt_app_lib
  PUBLIC
  cxx_std_20
)

target_include_directories(rt_app_lib
  PUBLIC
  ${CMAKE_CURRENT_SOURCE_DIR}/include
)

target_link_libraries(rt_app_lib
  PRIVATE
  Threads::Threads
  spdlog::spdlog
)
